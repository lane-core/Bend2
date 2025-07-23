{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

-- Eta-Form
-- ========
--
-- This module performs eta-reduction with lambda-inject optimization, transforming
-- nested lambda-match patterns into more efficient forms.
--
-- Basic Transformation:
-- --------------------
-- λx. λy. λz. (λ{...} x) ~> λ{0n:λy.λz.A; 1n+:λp.λy.λz.B}
--
-- The optimization moves intermediate lambdas inside match branches. It is
-- useful for the HVM backend due to linearization, and for the bidirectional
-- type-checker, which can't infer a form like `(λ{...} x)`.
--
-- Examples:
-- ---------
-- 1. Simple eta-reduction:
--    λn. (λ{0n:Z; 1n+:S} n) 
--    ----------------------
--    λ{0n:Z; 1n+:S}
--
-- 2. With intermediate lambdas:
--    λa. λb. (λ{0n:Z; 1n+:S} a) 
--    ---------------------------
--    λ{0n:λb.Z; 1n+:λp.λb.(S p)}
--
-- 3. List pattern:
--    λx. λy. (λ{[]:N; <>:C} x)
--    -------------------------
--    λ{[]:λy.N; <>:λh.λt.λy.(C h t)}
--
-- 4. Nested matches:
--    λa. λb. (λ{0n:(λ{0n:T; 1n+:F} b); 1n+:λa_.(λ{0n:F; 1n+:E} b)} a)
--    ----------------------------------------------------------------
--    λ{0n:λ{0n:T; 1n+:F}; 1n+:λa_.λ{0n:F; 1n+:E}}
--
-- 5. With existing field lambdas:
--    λa. λb. (λ{0n:Z; 1n+:λp.S} a)
--    -----------------------------
--    λ{0n:λb.Z; 1n+:λp.λb.S}
--
-- Key Points:
-- ----------
-- - Field lambdas (for constructor arguments) are injected first
-- - Intermediate lambdas are injected after field lambdas
-- - Existing field lambdas are preserved, not duplicated
-- - Field names use underscore prefix (_p, _h, _t) to avoid capture
-- - The transformation preserves semantics while enabling optimizations

{-# LANGUAGE ViewPatterns #-}

module Core.EtaForm where

import Core.Type
import qualified Data.Set as S
import Debug.Trace

-- Main eta-reduction function with lambda-inject optimization
etaForm :: Int -> Term -> Term
etaForm d t = case t of
  -- Check for the lambda-inject pattern: λx. λx0. λx1. ... (λ{...} x)
  Lam n ty f ->
    case isEtaLong n d (f (Var n d)) of
      Just (lmat, lams) -> etaForm d (injectLams lams lmat)
      Nothing           -> Lam n (fmap (etaForm d) ty) (\v -> etaForm (d+1) (f v))
  
  -- Recursive cases for all other constructors
  Var n i      -> Var n i
  Ref n i      -> Ref n i
  Sub t'       -> Sub (etaForm d t')
  Fix n f      -> Fix n (\v -> etaForm (d+1) (f v))
  Let k mt v f -> Let k (fmap (etaForm d) mt) (etaForm d v) (\v' -> etaForm (d+1) (f v'))
  Set          -> Set
  Chk a b      -> Chk (etaForm d a) (etaForm d b)
  Emp          -> Emp
  EmpM         -> EmpM
  Uni          -> Uni
  One          -> One
  UniM a       -> UniM (etaForm d a)
  Bit          -> Bit
  Bt0          -> Bt0
  Bt1          -> Bt1
  BitM a b     -> BitM (etaForm d a) (etaForm d b)
  Nat          -> Nat
  Zer          -> Zer
  Suc n        -> Suc (etaForm d n)
  NatM a b     -> NatM (etaForm d a) (etaForm d b)
  Lst t'       -> Lst (etaForm d t')
  Nil          -> Nil
  Con h t'     -> Con (etaForm d h) (etaForm d t')
  LstM a b     -> LstM (etaForm d a) (etaForm d b)
  Enu ss       -> Enu ss
  Sym s        -> Sym s
  EnuM cs e    -> EnuM [(s, etaForm d v) | (s,v) <- cs] (etaForm d e)
  Num nt       -> Num nt
  Val nv       -> Val nv
  Op2 o a b    -> Op2 o (etaForm d a) (etaForm d b)
  Op1 o a      -> Op1 o (etaForm d a)
  Sig a b      -> Sig (etaForm d a) (etaForm d b)
  Tup a b      -> Tup (etaForm d a) (etaForm d b)
  SigM a       -> SigM (etaForm d a)
  All a b      -> All (etaForm d a) (etaForm d b)
  App f x      -> App (etaForm d f) (etaForm d x)
  Eql t' a b   -> Eql (etaForm d t') (etaForm d a) (etaForm d b)
  -- Rfl          -> Rfl
  Rwt e g h    -> Rwt (etaForm d e) (etaForm d g) (etaForm d h)
  Met n t' cs  -> Met n (etaForm d t') (map (etaForm d) cs)
  Era          -> Era
  Sup l a b    -> Sup (etaForm d l) (etaForm d a) (etaForm d b)
  SupM l f'    -> SupM (etaForm d l) (etaForm d f')
  Loc s t'     -> Loc s (etaForm d t')
  Log s x      -> Log (etaForm d s) (etaForm d x)
  Pri p        -> Pri p
  Pat ss ms cs -> Pat (map (etaForm d) ss) [(k, etaForm d v) | (k,v) <- ms] [(map (etaForm d) ps, etaForm d rhs) | (ps,rhs) <- cs]
  Frk l a b    -> Frk (etaForm d l) (etaForm d a) (etaForm d b)

-- Check if a term matches the eta-long pattern: λx0. λx1. ... (λ{...} x)
isEtaLong :: Name -> Int -> Term -> Maybe (Term, [(Name, Maybe Term)])
isEtaLong target depth = go [] depth
  where
    go :: [(Name, Maybe Term)] -> Int -> Term -> Maybe (Term, [(Name, Maybe Term)])
    go lams d term = case cut term of
      -- Found more intermediate lambdas
      Lam n ty f -> 
        go (lams ++ [(n, ty)]) (d+1) (f (Var n d))
      
      -- Found application - check if it's (λ{...} x)
      App f arg ->
        case (cut f, cut arg) of
          -- Check if f is a lambda-match and arg is our target variable
          (lmat, Var v_n _) | v_n == target && isLambdaMatch lmat ->
            -- Also verify target variable is not free in the lambda-match
            if target `S.member` freeVars S.empty lmat
            then Nothing
            else Just (lmat, lams)
          _ -> Nothing
      
      -- Any other form doesn't match our pattern
      _ -> Nothing

-- Inject lambdas into each case of a lambda-match
injectLams :: [(Name, Maybe Term)] -> Term -> Term
injectLams lams term = case term of
  -- Empty match - no cases to inject into
  EmpM -> EmpM
  
  -- Unit match - inject lambdas into the single case
  UniM f -> UniM (injectLamsBody [] lams f)
  
  -- Bool match - inject lambdas into both cases
  BitM f t -> BitM (injectLamsBody [] lams f) (injectLamsBody [] lams t)
  
  -- Nat match - special handling for successor case (1 field)
  NatM z s -> NatM (injectLamsBody [] lams z) (injectLamsBody ["_p"] lams s)
  
  -- List match - special handling for cons case (2 fields)
  LstM n c -> LstM (injectLamsBody [] lams n) (injectLamsBody ["_h", "_t"] lams c)
  
  -- Enum match - inject into each case and default
  EnuM cs e -> EnuM [(s, injectLamsBody [] lams v) | (s,v) <- cs] (injectLamsBody [] lams e)
  
  -- Sigma match - special handling for pair case (2 fields)
  SigM f -> SigM (injectLamsBody ["_a", "_b"] lams f)
  
  -- Superposition match - special handling (2 fields)
  SupM l f -> SupM l (injectLamsBody ["_a", "_b"] lams f)
  
  -- Not a lambda-match
  _ -> term

-- Helper to inject lambdas, skipping existing field lambdas
injectLamsBody :: [Name] -> [(Name, Maybe Term)] -> Term -> Term
injectLamsBody fields lams body = go 0 fields lams body where
    go :: Int -> [Name] -> [(Name, Maybe Term)] -> Term -> Term
    go d []     lams body = foldr (\(n,ty) b -> Lam n ty (\_ -> b)) body lams
    go d (f:fs) lams body = case cut body of
      Lam n ty b -> Lam n ty (\v -> go (d+1) fs lams (b v))
      _          -> Lam f Nothing (\v -> go (d+1) fs lams (App body v))

-- Check if a term is a lambda-match (one of the match constructors)
isLambdaMatch :: Term -> Bool
isLambdaMatch term = case term of
  EmpM       -> True
  UniM _     -> True
  BitM _ _   -> True
  NatM _ _   -> True
  LstM _ _   -> True
  EnuM _ _   -> True
  SigM _     -> True
  SupM _ _   -> True
  _          -> False


-- testEtaForm :: IO ()
-- testEtaForm = do
  -- let term = Lam "a" (Just Nat) $ \a ->
             -- Lam "b" (Just Nat) $ \b ->
             -- App (NatM 
                   -- (App (NatM Bt1 (Lam "b" (Just Nat) $ \_ -> Bt0)) b)
                   -- (Lam "a" (Just Nat) $ \a' ->
                     -- App (NatM Bt0 (Lam "b" (Just Nat) $ \b' ->
                       -- App (App (Ref "eql") a') b')) b))
                 -- a
  -- putStrLn "Original term:"
  -- putStrLn $ show term
  -- putStrLn "\nAfter etaForm:"
  -- putStrLn $ show (etaForm 0 term)

-- this file works very well! good job. let's now just document it...


















-- AI logs (TODO: remove later)

-- PROBLEM: the function above is doing a simple eta-reduce transformation:
-- λx. (λ{ 0n:Z 1n+:S } x) ~> λ{ 0n:Z 1n+:S }
-- sadly, this transformation doesn't include the *lambda-inject optimization*.
-- the lambda inject optimization super-eta-reduces a wider range of forms:
-- λx. λv0. λv1. ... λvN. (λ{ 0n:Z 1n+:S } x)
-- is super-eta-reduced to:
-- λ{ 0n:λv0.λv1.Z 1n+:λp.λv0.λv1.(S p) }
-- specifically, it allows a number of lambdas to be placed between the
-- eta-removed lambda, and the application of the inner lambda-match to its
-- argument, x. when that happens, the whole expression is converted to the
-- inner lambda-match, with each "in-between" lambda moved to inside each
-- branch. note that, since some branches have fields (ex: the 1n+ branch has 1
-- field - the Nat predecessor), we must make sure the injected lambdas come
-- AFTER the field lambda. to do so, we *eta-expand* the case with one lambda
-- for each field, and we then apply it to each lambda. so, for example, the S
-- case became λp.λv0.λv1.(S p): i.e., a field lambda, followed by the
-- in-between injected lambdas, followed by the case body applied to each field
-- lambda variable.
-- 
-- examples:
-- 
-- λn:Nat. (λ{0n:0n;1n+:λ_x2:Nat. (λ{0n:0n;1n+:λp:Nat. 1n+div2(p)})(_x2)})(n)
-- should be converted to:
-- λn:Nat. (λ{0n:0n;1n+:λ_x2:Nat. (λ{0n:0n;1n+:λp:Nat. 1n+div2(p)})(_x2)})(n)
-- 
-- λa:Nat. λb:Nat. (λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)
-- should be converted to:
-- λ{0n:λb:Nat.(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. λb:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)}
-- which is further converted to:
-- λ{0n:λ{0n:True;1n+:λb:Nat. False};1n+:λa:Nat. λ{0n:False;1n+:λb:Nat. eql(a,b)}}
-- 
-- IMPLEMENTATION
-- 
-- to implement this algorithm, we proceed as follows:
-- 
-- the etaForm function will recursively traverse the term, reaching all sub-expressions
-- then, when it finds an expression in the form:
-- λx. λx0. λx1. ... (λ{...} x)
-- where:
-- - 'λx.' is a lambda binding a variable with a given name x
-- - 'λx0. λx1. ...' is a sequence of N lambdas
-- - '(λ{...} x)' is an application of a λ-match to a variable also *named* x
-- it will perform the transformation.
--
-- to identify that specific form, we will create a function:
-- isEtaLong :: ... -> Maybe (Term, [(String, Maybe Term)])
-- which will receive a term, and return either Nothing, or Just of:
-- - 'lmat': the λ-match (here, 'λ{...}')
-- - 'lams': the name/types of the in-between lambdas (here, '("x0",Nothing)' and '("x1",Nothing)')
-- 
-- when isEtaLong returns Just, the etaForm function will return:
-- etaForm (injectLams lams lmat)
-- the injectLams function injects the in-between lambdas on every case of the lmat.
-- it works in a per case-basis:
-- on BitM, it just injects each lambda on each case. example:
-- injectLams ["x0","x1"] λ{ True: A False: B }
-- becomes:
-- λ{ True: λx0. λx1. A False: λx0. λx1. B }
-- on LstM, it works similarly, but adding two extra lambdas: λh. and λh., on the Cons case. example:
-- injectLams ["x0","x1"] λ{ []: A <>: B }
-- becomes:
-- λ{ []: λx0. λx1. A <>: λh. λt. λx0. λx1. ((B x0) x1) }
-- notice that the field lambdas (λh. λt.) were injected first, then the in-between lambas, and then we applied the whole case to a Var of each in-between lambda.
-- 
-- this completes the algorithm - nothing else is needed.
-- note there is NO 'subst' needed in this implementation.
-- there is no lifting either. the binders introduced in the body are guaranteed
-- to be name-capture free, because they existed outside previously; we're merely
-- moving them down.
--
-- now, write below the COMPLETE EtaForm module.



-- output:
-- λa:Nat. λb:Nat. (λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)
-- λ{0n:λ{0n:True;1n+:λp. (λb:Nat. False)(p)};1n+:λp. λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p,b)}

-- reimplement the file above, but, this time, with rich debugging information (with trace),
-- allowing us to observe the algorithm step by step, and find where it went wrong.


-- Original term:
-- λa:Nat. λb:Nat. (λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)

-- After etaForm:
-- etaForm at depth 0: λa:Nat. λb:Nat. (λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)
-- Checking lambda a with body: λb:Nat. (λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)
-- isEtaLong checking for a in: λb:Nat. (λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)
  -- go with lams=[], term=λb:Nat. (λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)
  -- Found intermediate lambda: b
  -- go with lams=["b"], term=(λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)})(a)
  -- Found app: f=λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)}, arg=a
  -- Matched! lmat=λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)}, checking free vars...
  -- Success!
-- injectLams with lams=["b"] into: λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)}
-- mkLams creating lambdas ["b"] around: (λ{0n:True;1n+:λb:Nat. False})(b)
-- injectNatSucc with lams=["b"], s=λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)
-- mkLams creating lambdas ["b"] around: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
  -- NatM: z'=λb:Nat. (λ{0n:True;1n+:λb:Nat. False})(b), s'=λp. λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- mkLams creating lambdas ["b"] around: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- Found eta-long pattern! lmat: λ{0n:(λ{0n:True;1n+:λb:Nat. False})(b);1n+:λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)}, lams: [("b",Just Nat)], result: λ{0n:λb:Nat. (λ{0n:True;1n+:λb:Nat. False})(b);1n+:λp. λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)}
-- mkLams creating lambdas ["b"] around: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- etaForm at depth 0: λ{0n:λb:Nat. (λ{0n:True;1n+:λb:Nat. False})(b);1n+:λp. λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)}
-- etaForm at depth 0: λb:Nat. (λ{0n:True;1n+:λb:Nat. False})(b)
-- Checking lambda b with body: (λ{0n:True;1n+:λb:Nat. False})(b)
-- isEtaLong checking for b in: (λ{0n:True;1n+:λb:Nat. False})(b)
  -- go with lams=[], term=(λ{0n:True;1n+:λb:Nat. False})(b)
  -- Found app: f=λ{0n:True;1n+:λb:Nat. False}, arg=b
  -- Matched! lmat=λ{0n:True;1n+:λb:Nat. False}, checking free vars...
  -- Success!
-- injectLams with lams=[] into: λ{0n:True;1n+:λb:Nat. False}
-- mkLams creating lambdas [] around: True
-- injectNatSucc with lams=[], s=λb:Nat. False
-- mkLams creating lambdas [] around: (λb:Nat. False)(p)
  -- NatM: z'=True, s'=λp. (λb:Nat. False)(p)
-- mkLams creating lambdas [] around: (λb:Nat. False)(p)
-- Found eta-long pattern! lmat: λ{0n:True;1n+:λb:Nat. False}, lams: [], result: λ{0n:True;1n+:λp. (λb:Nat. False)(p)}
-- mkLams creating lambdas [] around: (λb:Nat. False)(p)
-- etaForm at depth 0: λ{0n:True;1n+:λp. (λb:Nat. False)(p)}
-- etaForm at depth 0: True
-- mkLams creating lambdas [] around: (λb:Nat. False)(p)
-- etaForm at depth 0: λp. (λb:Nat. False)(p)
-- mkLams creating lambdas [] around: (λb:Nat. False)(p)
-- Checking lambda p with body: (λb:Nat. False)(p)
-- isEtaLong checking for p in: (λb:Nat. False)(p)
  -- go with lams=[], term=(λb:Nat. False)(p)
  -- Found app: f=λb:Nat. False, arg=p
  -- No match
-- No eta-long pattern found
-- mkLams creating lambdas [] around: (λb:Nat. False)(p)
-- etaForm at depth 1: (λb:Nat. False)(p)
-- etaForm at depth 1: λb:Nat. False
-- Checking lambda b with body: False
-- isEtaLong checking for b in: False
  -- go with lams=[], term=False
  -- Not an app or lam
-- No eta-long pattern found
-- etaForm at depth 1: Nat
-- etaForm at depth 2: False
-- etaForm at depth 1: p
-- mkLams creating lambdas ["b"] around: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- etaForm at depth 0: λp. λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- mkLams creating lambdas ["b"] around: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- Checking lambda p with body: λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- isEtaLong checking for p in: λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
  -- go with lams=[], term=λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
  -- Found intermediate lambda: b
  -- go with lams=["b"], term=(λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
  -- Found app: f=λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b), arg=p
-- No eta-long pattern found
-- mkLams creating lambdas ["b"] around: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- etaForm at depth 1: λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- Checking lambda b with body: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- isEtaLong checking for b in: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
  -- go with lams=[], term=(λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
  -- Found app: f=λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b), arg=p
-- No eta-long pattern found
-- etaForm at depth 1: Nat
-- etaForm at depth 2: (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)
-- etaForm at depth 2: λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)
-- Checking lambda a with body: (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)
-- isEtaLong checking for a in: (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)
  -- go with lams=[], term=(λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)
  -- Found app: f=λ{0n:False;1n+:λb:Nat. eql(a,b)}, arg=b
-- No eta-long pattern found
-- etaForm at depth 2: Nat
-- etaForm at depth 3: (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b)
-- etaForm at depth 3: λ{0n:False;1n+:λb:Nat. eql(a,b)}
-- etaForm at depth 3: False
-- etaForm at depth 3: λb:Nat. eql(a,b)
-- Checking lambda b with body: eql(a,b)
-- isEtaLong checking for b in: eql(a,b)
  -- go with lams=[], term=eql(a,b)
  -- Found app: f=eql(a), arg=b
-- No eta-long pattern found
-- etaForm at depth 3: Nat
-- etaForm at depth 4: eql(a,b)
-- etaForm at depth 4: eql(a)
-- etaForm at depth 4: eql
-- etaForm at depth 4: a
-- etaForm at depth 4: b
-- etaForm at depth 3: b
-- etaForm at depth 2: p
-- λ{0n:λ{0n:True;1n+:λp. (λb:Nat. False)(p)};1n+:λp. λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)}
-- λ{0n:λ{0n:True;1n+:λp. λb:Nat. False};1n+:λp. λb:Nat. (λa:Nat. (λ{0n:False;1n+:λb:Nat. eql(a,b)})(b))(p)}


-- what went wrong?

-- Looking at the debug output, the issue is in how we handle the injection of lambdas.
-- When we have a pattern like:
-- λa. λb. (λ{0n:Z;1n+:λa. S})(a)
-- 
-- We want to transform it to:
-- λ{0n:λb.Z;1n+:λp. λb. S[a:=p]}
-- 
-- But the current implementation produces:
-- λ{0n:λb.Z;1n+:λp. λb. (λa. S)(p)}
-- 
-- The problem is that we're not properly substituting the pattern variable.
-- Instead of applying (λa. S) to p, we should be doing a substitution of a with p in S.
-- 
-- However, since our implementation doesn't use explicit substitution, we need to
-- rethink the approach. The issue is that when we inject lambdas into a case that
-- already has a lambda (like the successor case), we're creating an application
-- instead of properly threading the variables through.

-- instead of a substitution, let's make the injectLams function smarter.
-- previously, a pattern like:
-- injectLams ["x0","x1"] λ{ []: A <>: B }
-- would be transformed into:
-- λ{ []: λx0. λx1. A <>: λh. λt. λx0. λx1. ((B x0) x1) }
-- regardless of what B is. now, instead, when injecting fial lambdas, let's try
-- to detect if these are already present. if so, we just skip the existing fields.
-- so, for example, in:
-- injectLams ["x0","x1"] λ{ []: A <>: λa. λb. B }
-- we would produce:
-- λ{ []: λx0. λx1. A <>: λa. λb. λx0. λx1. B }
-- note that we merely skip the λa. λb. field-binding lambdas.
-- no renaming, no substitutions.
-- to do this properly, I suggeset that you update the function responsible for
-- the injection of the in-between lambdas. that function must receive the field
-- lambdas as an *extra* argument. then, it must compare. example:
-- injectLamsBody ["h","t"] ["x0","x1"] B =>
-- λh. injectLamsBody ["t"] ["x0","x1"] (B h) =>
-- λh. λt. injectLamsBody [] ["x0","x1"] ((B h) t) =>
-- λh. λt. λx0. injectLamsBody [] ["x1"] ((B h) t) =>
-- λh. λt. λx0. λx1. injectLamsBody [] [] ((B h) t) =>
-- λh. λt. λx0. λx1. ((B h) t) =>
-- or, in the case with existing field lambdas:
-- injectLamsBody ["h","t"] ["x0","x1"] λH.λT.B =>
-- λH. injectLamsBody ["t"] ["x0","x1"] λT.B =>
-- λH. λT. injectLamsBody [] ["x0","x1"] B =>
-- λH. λT. λx0. injectLamsBody [] ["x1"] B =>
-- λH. λT. λx0. λx1. injectLamsBody [] [] B =>
-- λH. λT. λx0. λx1. B =>
-- notice how we just skip when there is already a lambda.
-- does that make sense?
-- if so, re-implement the file to take this into account.
-- if not, tell me why.

-- Yes, that makes perfect sense! The issue is that we're creating unnecessary lambda applications
-- when the field lambdas already exist. Let me reimplement with this approach.

-- The file below works!
-- Now, write a comprehensive documentation of this file, below.
-- Explain what it does, how it works, including examples and implementation details.
-- Make sure to include all the quirks that make it work, but make it concise and non-repetitive.
-- Basically, make sure the important info is there for someone in the future trying to understand
-- what this file is, and also to make sure that whoever refactors it doesn't accidentally remove
-- important details. But don't make it too verbose, just the minimal info needed.
