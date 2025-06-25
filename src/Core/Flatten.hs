{-./Type.hs-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

-- Pattern Matching Flattener
-- ==========================
-- 
-- This algorithm converts pattern matching expressions with multiple 
-- scrutinees into nested case trees with single scrutinees. Example:
--
-- match x y
-- | 0n     0n          = X0
-- | (1n+x) 0n          = X1
-- | 0n     (1n+y)      = X2
-- | (1n+x) (1n+0n)     = X3
-- | (1n+x) (1n+(1n+z)) = X4
-- ------------------------- flatten
-- match x:
--   case 0n:
--     match y:
--       case 0n: X0
--       case 1+y: X2
--   case 1n+x:
--     match y:
--       case 0n: X1
--       case 1n+y_:
--         match y_:
--           case 0n: X3
--           case 1n+z: X4

module Core.Flatten where

import Data.List (nub, find)
import qualified Data.Map as M

import Debug.Trace

import Core.Type

-- Flattener
-- =========
-- Converts pattern-matches into if-lets, forcing the shape:
--   match x { with ... ; case @C: ... ; case x: ... }
-- After this transformation, the match will have exactly:
-- - 1 scrutinee
-- - 1 value case
-- - 1 default case
-- Outer scrutinees will be moved inside via 'with'.

flatten :: Int -> Term -> Term
flatten d (Var n i)   = Var n i
flatten d (Ref n)     = Ref n
flatten d (Sub t)     = Sub (flatten d t)
flatten d (Fix n f)   = Fix n (\x -> flatten (d+1) (f x))
flatten d (Let v f)   = Let (flatten d v) (flatten d f)
flatten d Set         = Set
flatten d (Ann x t)   = Ann (flatten d x) (flatten d t)
flatten d (Chk x t)   = Chk (flatten d x) (flatten d t)
flatten d Emp         = Emp
flatten d Efq         = Efq
flatten d Uni         = Uni
flatten d One         = One
flatten d (Use f)     = Use (flatten d f)
flatten d Bit         = Bit
flatten d Bt0         = Bt0
flatten d Bt1         = Bt1
flatten d (Bif f t)   = Bif (flatten d f) (flatten d t)
flatten d Nat         = Nat
flatten d Zer         = Zer
flatten d (Suc n)     = Suc (flatten d n)
flatten d (Swi z s)   = Swi (flatten d z) (flatten d s)
flatten d (Lst t)     = Lst (flatten d t)
flatten d Nil         = Nil
flatten d (Con h t)   = Con (flatten d h) (flatten d t)
flatten d (Mat n c)   = Mat (flatten d n) (flatten d c)
flatten d (Enu s)     = Enu s
flatten d (Sym s)     = Sym s
flatten d (Cse c e)   = Cse [(s, flatten d t) | (s, t) <- c] (flatten d e)
flatten d (Sig a b)   = Sig (flatten d a) (flatten d b)
flatten d (Tup a b)   = Tup (flatten d a) (flatten d b)
flatten d (Get f)     = Get (flatten d f)
flatten d (All a b)   = All (flatten d a) (flatten d b)
flatten d (Lam n f)   = Lam n (\x -> flatten (d+1) (f x))
flatten d (App f x)   = App (flatten d f) (flatten d x)
flatten d (Eql t a b) = Eql (flatten d t) (flatten d a) (flatten d b)
flatten d Rfl         = Rfl
flatten d (Rwt f)     = Rwt (flatten d f)
flatten d (Met i t x) = Met i (flatten d t) (map (flatten d) x)
flatten d (Ind t)     = Ind (flatten d t)
flatten d (Frz t)     = Frz (flatten d t)
flatten d Era         = Era
flatten d (Sup l a b) = Sup l (flatten d a) (flatten d b)
flatten d (Num t)     = Num t
flatten d (Val v)     = Val v
flatten d (Op2 o a b) = Op2 o (flatten d a) (flatten d b)
flatten d (Op1 o a)   = Op1 o (flatten d a)
flatten d (Pri p)     = Pri p
flatten d (Loc s t)   = Loc s (flatten d t)
flatten d (Pat s m c) = simplify d $ flattenPat d (Pat s m c)

flattenPat :: Int -> Term -> Term
flattenPat d pat@(Pat (s:ss) ms ((((strip->Var k i):ps),rhs):cs)) =
  trace (">> var: " ++ show pat) $
  Pat ss ((k,s):ms) (joinVarCol (d+1) k (((Var k i:ps),rhs):cs))
flattenPat d pat@(Pat (s:ss) ms cs@((((strip->p):_),_):_)) =
  trace (">> ctr: " ++ show pat) $
  Pat [s] moves [([ct], picks), ([var d], drops)] where
    (ct,fs) = ctrOf d p
    (ps,ds) = peelCtrCol ct cs
    moves   = ms ++ map (\ (s,i) -> (patOf (d+i) s, s)) (zip ss [0..])
    picks   = flatten d' (Pat (fs   ++ ss) ms ps) where d' = d + length fs
    drops   = flatten d' (Pat (var d : ss) ms ds) where d' = d + 1
flattenPat d pat = pat

-- Converts an all-variable column to a 'with' statement
-- match x y { case x0 @A: F(x0) ; case x1 @B: F(x1) }
-- --------------------------------------------------- joinVarCol k
-- match y { with k=x case @A: F(k) ; case @B: F(k) }
joinVarCol :: Int -> Name -> [Case] -> [Case]
joinVarCol d k ((((strip->Var j _):ps),rhs):cs) = (ps, subst j (Var k 0) rhs) : joinVarCol d k cs
joinVarCol d k ((((strip->ctr    ):ps),rhs):cs) = error "redundant pattern"
joinVarCol d k cs                               = cs

-- Peels a constructor layer from a column
-- match x y:
--   case @Z{}      @A: A
--   case @S{@Z}    @B: B
--   case @S{@S{p}} @C: C(p)
-- ------------------------- peel @Z , peel @S{k}
-- match x:
--   with y
--   case @Z: # ↓ peel @Z
--     match y:
--       case @A: A
--   case @S{k}: # ↓ peel @S{k}
--     match k y:
--       case @Z    @B: B
--       case @S{p} @C: C(p)
peelCtrCol :: Term -> [Case] -> ([Case],[Case])
peelCtrCol (strip->k) ((((strip->p):ps),rhs):cs) = 
  -- trace (">> peel " ++ show k ++ " ~ " ++ show p) $
  case (k,p) of
    (Zer   , Zer  )   -> ((ps, rhs) : picks , drops)
    (Zer   , Var k _) -> ((ps, subst k Zer rhs) : picks , ((p:ps),rhs) : drops)
    (Suc _ , Suc x)   -> (((x:ps), rhs) : picks , drops)
    (Suc _ , Var k _) -> (((Var k 0:ps), subst k (Suc (Var k 0)) rhs) : picks , ((p:ps),rhs) : drops)
    x                 -> (picks , ((p:ps),rhs) : drops)
  where (picks, drops) = peelCtrCol k cs
peelCtrCol k cs = (cs,cs)

flattenBook :: Book -> Book
flattenBook (Book defs) = Book (M.map flattenDefn defs)
  where flattenDefn (i, x, t) = (i, flatten 0 x, flatten 0 t)

-- Simplify
-- ========
-- Removes redundant matches, adjusts form

-- Substitutes a move list into an expression
shove :: Int -> [Move] -> Term -> Term
shove d ms term = foldr (\ (k,v) x -> subst k v x) term ms 

-- Converts zero-scrutinee matches to plain expressions
-- match { with x=A ... case: F(x,...) ... }
-- ----------------------------------------- decay
-- F(A,...)
decay :: Int -> Term -> Term
decay d (Pat [] ms (([],rhs):cs)) = decay d (shove d ms rhs)
decay d term                      = term

-- Merges redundant case-match chains into parent
-- match ... { ... case x: match x { case A:A ; case B:B ... } ... }
-- ----------------------------------------------------------------- merge
-- match ... { ... case A:A ; case B:B ... }
merge :: Int -> Term -> Term
merge d (Pat ss ms cs) = Pat ss ms (cases cs) where 
  cases :: [Case] -> [Case]
  cases (([Var x _], (Pat [Var x' _] ms cs')) : cs)
    | x == x' = csA ++ csB
    where csA = map (\ (p, rhs) -> (p, merge d (shove d ms rhs))) cs'
          csB = cases cs
  cases ((p,rhs):cs) = (p, merge d rhs) : cases cs
  cases []           = []
merge d term = term

simplify :: Int -> Term -> Term
simplify d = merge d . decay d

-- UnPat
-- =====
-- Converts all Pats to native λ-matches.

unpat :: Int -> Term -> Term
unpat d (Var n i)       = Var n i
unpat d (Ref n)         = Ref n
unpat d (Sub t)         = Sub (unpat d t)
unpat d (Fix n f)       = Fix n (\x -> unpat (d+1) (f x))
unpat d (Let v f)       = Let (unpat d v) (unpat d f)
unpat d Set             = Set
unpat d (Ann x t)       = Ann (unpat d x) (unpat d t)
unpat d (Chk x t)       = Chk (unpat d x) (unpat d t)
unpat d Emp             = Emp
unpat d Efq             = Efq
unpat d Uni             = Uni
unpat d One             = One
unpat d (Use f)         = Use (unpat d f)
unpat d Bit             = Bit
unpat d Bt0             = Bt0
unpat d Bt1             = Bt1
unpat d (Bif f t)       = Bif (unpat d f) (unpat d t)
unpat d Nat             = Nat
unpat d Zer             = Zer
unpat d (Suc n)         = Suc (unpat d n)
unpat d (Swi z s)       = Swi (unpat d z) (unpat d s)
unpat d (Lst t)         = Lst (unpat d t)
unpat d Nil             = Nil
unpat d (Con h t)       = Con (unpat d h) (unpat d t)
unpat d (Mat n c)       = Mat (unpat d n) (unpat d c)
unpat d (Enu s)         = Enu s
unpat d (Sym s)         = Sym s
unpat d (Cse c e)       = Cse [(s, unpat d t) | (s, t) <- c] (unpat d e)
unpat d (Sig a b)       = Sig (unpat d a) (unpat d b)
unpat d (Tup a b)       = Tup (unpat d a) (unpat d b)
unpat d (Get f)         = Get (unpat d f)
unpat d (All a b)       = All (unpat d a) (unpat d b)
unpat d (Lam n f)       = Lam n (\x -> unpat (d+1) (f x))
unpat d (App f x)       = App (unpat d f) (unpat d x)
unpat d (Eql t a b)     = Eql (unpat d t) (unpat d a) (unpat d b)
unpat d Rfl             = Rfl
unpat d (Rwt f)         = Rwt (unpat d f)
unpat d (Met i t x)     = Met i (unpat d t) (map (unpat d) x)
unpat d (Ind t)         = Ind (unpat d t)
unpat d (Frz t)         = Frz (unpat d t)
unpat d Era             = Era
unpat d (Sup l a b)     = Sup l (unpat d a) (unpat d b)
unpat d (Num t)         = Num t
unpat d (Val v)         = Val v
unpat d (Op2 o a b)     = Op2 o (unpat d a) (unpat d b)
unpat d (Op1 o a)       = Op1 o (unpat d a)
unpat d (Pri p)         = Pri p
unpat d (Loc s t)       = Loc s (unpat d t)
unpat d (Pat [s] ms cs) = unpatPat d s ms cs
unpat d (Pat ss  ms cs) = error "unpat: multiple scrutinees after flattening"

-- unpatPat :: Int -> Term -> [Move] -> [Case] -> Term
-- unpatPat d s ms (([Zer],z):([Suc p],st):cs) =
  -- unmove d ms $ Swi (unpat d z) (Lam (patOf d p) $ \x -> unpat (d+1) (subst (patOf d p) x st))
-- unpatPat d s ms (([Suc p],st):([Zer],z):cs) =
  -- unmove d ms $ Swi (unpat d z) (Lam (patOf d p) $ \x -> unpat (d+1) (subst (patOf d p) x st))
-- unpatPat d s ms (([Zer],z):([Var k i],v):cs) =
  -- unmove d ms $ Swi (unpat d z) (Lam k $ \x -> unpat (d+1) (subst k (Suc x) v))
-- unpatPat d s ms (([Suc p],st):([Var k i],v):cs) =
  -- unmove d ms $ Swi (unpat d (subst k Zer v)) (Lam (patOf d p) $ \x -> unpat (d+1) (subst (patOf d p) x st))
-- unpatPat d s ms (([Bt0],f):([Bt1],t):cs) =
  -- unmove d ms $ Bif (unpat d f) (unpat d t)
-- unpatPat d s ms (([Bt1],t):([Bt0],f):cs) =
  -- unmove d ms $ Bif (unpat d f) (unpat d t)
-- unpatPat d s ms (([Bt0],f):([Var k i],v):cs) =
  -- unmove d ms $ Bif (unpat d f) (unpat d (subst k Bt1 v))
-- unpatPat d s ms (([Bt1],t):([Var k i],v):cs) =
  -- unmove d ms $ Bif (unpat d (subst k Bt0 v)) (unpat d t)
-- unpatPat d s ms (([Nil],n):([Con h t],c):cs) =
  -- unmove d ms $ Mat (unpat d n) (Lam (patOf d h) $ \h' -> Lam (patOf d t) $ \t' ->
    -- unpat (d+2) (subst (patOf d h) h' (subst (patOf d t) t' c)))
-- unpatPat d s ms (([Con h t],c):([Nil],n):cs) =
  -- unmove d ms $ Mat (unpat d n) (Lam (patOf d h) $ \h' -> Lam (patOf d t) $ \t' ->
    -- unpat (d+2) (subst (patOf d h) h' (subst (patOf d t) t' c)))
-- unpatPat d s ms (([Nil],n):([Var k i],v):cs) =
  -- unmove d ms $ Mat (unpat d n) (Lam "h" $ \h' -> Lam "t" $ \t' ->
    -- unpat (d+2) (subst k (Con h' t') v))
-- unpatPat d s ms (([Con h t],c):([Var k i],v):cs) =
  -- unmove d ms $ Mat (unpat d (subst k Nil v)) (Lam (patOf d h) $ \h' -> Lam (patOf d t) $ \t' ->
    -- unpat (d+2) (subst (patOf d h) h' (subst (patOf d t) t' c)))
-- unpatPat d s ms (([One],u):cs) =
  -- unmove d ms $ Use (unpat d u)
-- unpatPat d s ms (([Tup a b],p):cs) =
  -- unmove d ms $ Get (Lam (patOf d a) $ \a' -> Lam (patOf d b) $ \b' ->
    -- unpat (d+2) (subst (patOf d a) a' (subst (patOf d b) b' p)))
-- unpatPat d s ms cs@(([Sym _],_):_) =
  -- let (symCases, def) = syms cs
      -- cses = [(sym, unpat d body) | (sym,body) <- symCases]
      -- dflt = maybe Era (unpat d) def
  -- in unmove d ms $ Cse cses dflt
  -- where syms :: [Case] -> ([(String,Term)], Maybe Term)
        -- syms []                    = ([], Nothing)
        -- syms (([Sym s]  ,body):cs) = let (rest, def) = syms cs in ((s, body) : rest, def)
        -- syms (([Var _ _],body):cs) = ([], Just body)
        -- syms cs                    = error $ "syms: invalid " ++ show cs
-- unpatPat d s ms (([Var k i],body):cs) =
  -- unpat d (shove d ((k,s):ms) body)
-- unpatPat d s ms [] =
  -- unmove d ms Efq
-- unpatPat d s ms _ = error "unpatPat: invalid pattern"


-- PROBLEM: the function above is WRONG - we forgot to apply the lambda-match to the scrutinee!
-- TASK: fix the function above. write the COMPLETE fixed version below

unpatPat :: Int -> Term -> [Move] -> [Case] -> Term
unpatPat d s ms (([Zer],z):([Suc p],st):cs) =
  matcher d ms s $ Swi (unpat d z) (Lam (patOf d p) $ \x -> unpat (d+1) (subst (patOf d p) x st))
unpatPat d s ms (([Suc p],st):([Zer],z):cs) =
  matcher d ms s $ Swi (unpat d z) (Lam (patOf d p) $ \x -> unpat (d+1) (subst (patOf d p) x st))
unpatPat d s ms (([Zer],z):([Var k i],v):cs) =
  matcher d ms s $ Swi (unpat d z) (Lam k $ \x -> unpat (d+1) (subst k (Suc x) v))
unpatPat d s ms (([Suc p],st):([Var k i],v):cs) =
  matcher d ms s $ Swi (unpat d (subst k Zer v)) (Lam (patOf d p) $ \x -> unpat (d+1) (subst (patOf d p) x st))
unpatPat d s ms (([Bt0],f):([Bt1],t):cs) =
  matcher d ms s $ Bif (unpat d f) (unpat d t)
unpatPat d s ms (([Bt1],t):([Bt0],f):cs) =
  matcher d ms s $ Bif (unpat d f) (unpat d t)
unpatPat d s ms (([Bt0],f):([Var k i],v):cs) =
  matcher d ms s $ Bif (unpat d f) (unpat d (subst k Bt1 v))
unpatPat d s ms (([Bt1],t):([Var k i],v):cs) =
  matcher d ms s $ Bif (unpat d (subst k Bt0 v)) (unpat d t)
unpatPat d s ms (([Nil],n):([Con h t],c):cs) =
  matcher d ms s $ Mat (unpat d n) (Lam (patOf d h) $ \h' -> Lam (patOf d t) $ \t' ->
    unpat (d+2) (subst (patOf d h) h' (subst (patOf d t) t' c)))
unpatPat d s ms (([Con h t],c):([Nil],n):cs) =
  matcher d ms s $ Mat (unpat d n) (Lam (patOf d h) $ \h' -> Lam (patOf d t) $ \t' ->
    unpat (d+2) (subst (patOf d h) h' (subst (patOf d t) t' c)))
unpatPat d s ms (([Nil],n):([Var k i],v):cs) =
  matcher d ms s $ Mat (unpat d n) (Lam "h" $ \h' -> Lam "t" $ \t' ->
    unpat (d+2) (subst k (Con h' t') v))
unpatPat d s ms (([Con h t],c):([Var k i],v):cs) =
  matcher d ms s $ Mat (unpat d (subst k Nil v)) (Lam (patOf d h) $ \h' -> Lam (patOf d t) $ \t' ->
    unpat (d+2) (subst (patOf d h) h' (subst (patOf d t) t' c)))
unpatPat d s ms (([One],u):cs) =
  matcher d ms s $ Use (unpat d u)
unpatPat d s ms (([Tup a b],p):cs) =
  matcher d ms s $ Get (Lam (patOf d a) $ \a' -> Lam (patOf d b) $ \b' ->
    unpat (d+2) (subst (patOf d a) a' (subst (patOf d b) b' p)))
unpatPat d s ms cs@(([Sym _],_):_) =
  let (symCases, def) = syms cs
      cses = [(sym, unpat d body) | (sym,body) <- symCases]
      dflt = maybe Era (unpat d) def
  in matcher d ms s $ Cse cses dflt
  where syms :: [Case] -> ([(String,Term)], Maybe Term)
        syms []                    = ([], Nothing)
        syms (([Sym s]  ,body):cs) = let (rest, def) = syms cs in ((s, body) : rest, def)
        syms (([Var _ _],body):cs) = ([], Just body)
        syms cs                    = error $ "syms: invalid " ++ show cs
unpatPat d s ms (([Var k i],body):cs) =
  unpat d (shove d ((k,s):ms) body)
unpatPat d s ms [] =
  matcher d ms s Efq
unpatPat d s ms _ = error "unpatPat: invalid pattern"

matcher :: Int -> [Move] -> Term -> Term -> Term
matcher d ms s (Swi z (Lam p f)) =
  apps d (map snd ms) (App swi s) where
    swi = Swi ifZ ifS
    ifZ = lams d (map fst ms) z
    ifS = Lam p $ \x -> lams d (map fst ms) (f x)
matcher d ms s (Bif f t) =
  apps d (map snd ms) (App bif s) where
    bif = Bif ifF ifT
    ifF = lams d (map fst ms) f
    ifT = lams d (map fst ms) t
matcher d ms s (Mat n (Lam h (unlam d -> Lam t (unlam d -> c)))) =
  apps d (map snd ms) (App mat s) where
    mat = Mat ifN ifC
    ifN = lams d (map fst ms) n
    ifC = Lam h $ \_ -> Lam t $ \_ -> lams d (map fst ms) c
matcher d ms s (Mat n c) =
  apps d (map snd ms) (App mat s) where
    mat = Mat ifN ifC
    ifN = lams d (map fst ms) n
    ifC = lams d (map fst ms) c
matcher d ms s (Use u) =
  apps d (map snd ms) (App use s) where
    use = Use ifU
    ifU = lams d (map fst ms) u
matcher d ms s (Get (Lam a (unlam d -> Lam b (unlam d -> p)))) =
  apps d (map snd ms) (App get s) where
    get = Get ifP
    ifP = Lam a $ \_ -> Lam b $ \_ -> lams d (map fst ms) p
matcher d ms s (Get f) =
  apps d (map snd ms) (App get s) where
    get = Get ifP
    ifP = lams d (map fst ms) f
matcher d ms s (Cse c e) =
  apps d (map snd ms) (App cse s) where
    cse = Cse [(s, lams d (map fst ms) t) | (s, t) <- c] (lams d (map fst ms) e)
matcher d ms s Efq =
  apps d (map snd ms) (App Efq s)
matcher d ms s other =
  error "TODO"

unpatBook :: Book -> Book
unpatBook (Book defs) = Book (M.map unpatDefn defs)
  where unpatDefn (i, x, t) = (i, unpat 0 x, unpat 0 t)

-- Helpers
-- -------

-- Creates a fresh name at given depth
fresh :: Int -> String
fresh d = "x" ++ show d

-- Creates a fresh variable at given depth
var :: Int -> Term
var d = Var (fresh d) d

-- Creates a fresh pattern at given depth
pat :: Int -> Term -> Term
pat d f = Var (patOf d f) d

-- Gets a var name, or creates a fresh one
patOf :: Int -> Term -> String
patOf d (strip->Var k i) = k
patOf d p                = fresh d

-- Returns a single-layer constructor, replacing fields by pattern variables
ctrOf :: Int -> Term -> (Term, [Term])
ctrOf d Zer     = (Zer , [])
ctrOf d (Suc p) = (Suc (pat d p), [pat d p])
ctrOf d x       = (var d , [var d])

-- Applies n arguments to a value
apps :: Int -> [Term] -> Term -> Term
apps d ms t = foldl (\ t x -> App t x) t ms

-- Extracts a lambda's body
unlam :: Int -> (Term -> Term) -> Term
unlam d f = f (var d)

-- Injects lambdas after skipping n lambdas
lams :: Int -> [Name] -> Term -> Term
lams d (k:ks) t = Lam k $ \_ -> lams (d+1) ks t
lams d []     t = t
