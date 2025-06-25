{-./Type.hs-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

-- Pattern Matching Flattener
-- ==========================
-- 
-- This algorithm converts pattern matching expressions with multiple 
-- scrutinees into nested case trees with single scrutinees.
--
-- Example transformation in Bend syntax:
--
-- match x y
-- | 0     0         = X0
-- | (↑x)  0         = X1
-- | 0     (↑y)      = X2
-- | (↑x)  (↑0)      = X3
-- | (↑x)  (↑(↑z))   = X4
--
-- Becomes:
--
-- match x:
--   case 0:
--     match y:
--       case 0:
--         X0
--       case 1+y:
--         X2
--   case 1+x:
--     match y:
--       case 0:
--         X1
--       case 1+y_:
--         match y_:
--           case 0:
--             X3
--           case 1+z:
--             X4
--
-- The algorithm works column-by-column from left to right:
-- 1. Take the first scrutinee and its column of patterns
-- 2. Group rules by constructor type (0/↑ for Nat, []/:: for List, etc.)
-- 3. For each constructor, extract its arguments and continue with remaining columns
-- 4. Variable patterns become default cases

module Core.Flatten where

import Data.List (nub, find)
import qualified Data.Map as M

import Debug.Trace

import Core.Type

-- Main Flattener
-- --------------

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
flatten d (Pat s m c) = flattenPat d (Pat s m c)

flattenBook :: Book -> Book
flattenBook (Book defs) = Book (M.map flattenDefn defs)
  where flattenDefn (i, x, t) = (i, flatten 0 x, flatten 0 t)

-- Pattern Match Flattening
-- ------------------------


-- match x y { with m ; case @Z @Z: @A ; case @Z @S{y}: @B(y) ; case @S{x} @Z: @C(x) ; case @S{x} @S{@Z}: @D(x,y) ; case @S{x} @S{@S{y}}: @E(x,y) }
-- ------------------------------------------------------------------------------------------------------------------------------------------------
-- match x { with m ; case @Z: (match y { with m ; case @Z: @A ; case @S{y}: @B(y) }) ; case @S{xp}: (match xp y { with m ; case }) }

-- match x: { case Z: A ; case S{x}: B ; case S{S{x}}: C }
-- -------------------------------------------------------
-- (Z => match { case: A } ; S{x} => match x { case S{x}: C ; case x: B } )

-- match x y { with m ; case @Z @Z: @A ; case @Z @S{y}: @B(y) ; case @S{x} @Z: @C(x) ; case @S{x} @S{@Z}: @D(x,y) ; case @S{x} @S{@S{y}}: @E(x,y) }
-- peel Z:
-- -- match y { with m ; case @Z: @A ; case @S{y}: @B(y) }
-- peel S{X}:
-- -- match X y { with m ; case x @Z: @C(x) ; case x @S{@Z}: @D(x,y) ; case x @S{@S{y}}: @E(x,y) }

-- match x { case @Z: A ; case @S{x}: B(x) ; case @S{@S{x}}: C(x) }
-- peel @Z:
--   match x {
--     @Z: match { case: A }
--     x : match x { case @S{x}: B(x) ; case @S{@S{x}}: C(x) }
--   }
-- peel @S{X}:
--    match x {
--      @S{X} : match X { case x: B(x) ; case @S{x}: C(x) }
--      x     : match x { case @Z: A }
--    }

type PMap = [(Term,[Case])] -- maps outer constructors to inner matches
data CtrV = ZerV | SucV

flattenPat :: Int -> Term -> Term
-- FIXME: check if all are vars, remove them without using 'map'
flattenPat d pat@(Pat (s:ss) ms ((((strip -> Var _ _):ps),rhs):cs)) =
  trace (show pat) $ flattenPat d (Pat ss ms ((ps,rhs) : map (\ (ps,rhs) -> (tail ps,rhs)) cs))
flattenPat d pat@(Pat (s:ss) ms ccs@(((p:_),_):_)) =
  trace (show pat) $ Pat [s] ms [([ct], picked), ([var d], dropped)] where
    (ct,fs) = ctrOf d (strip p)
    picked  = flatten d' (picks d' p (Pat (fs   ++ ss) ms ccs)) where d' = d + length fs
    dropped = flatten d' (drops d' p (Pat (var d : ss) ms ccs)) where d' = d + 1
flattenPat d pat = pat

picks :: Int -> Term -> Term -> Term
picks d k (Pat ss ms (((p:ps),rhs):cs)) =
  trace (">> picks: " ++ show k ++ " ~~ " ++ show p) $
  case (strip k , strip p) of
    (Zer     , Zer  ) -> pushCase (ps    ,rhs) (picks d k $ Pat ss ms cs)
    (Suc _   , Suc x) -> pushCase ((x:ps),rhs) (picks d k $ Pat ss ms cs)
    (Var _ _ , x    ) -> pushCase ((x:ps),rhs) (picks d k $ Pat ss ms cs)
    x                 -> picks d k $ Pat ss ms cs
picks d k pat = pat

drops :: Int -> Term -> Term -> Term
drops d k (Pat ss ms (((p:ps),rhs):cs)) =
  case (strip k , strip p) of
    (Zer     , Zer  ) -> drops d k $ Pat ss ms cs
    (Suc _   , Suc x) -> drops d k $ Pat ss ms cs
    (Var _ _ , x    ) -> drops d k $ Pat ss ms cs
    _                 -> pushCase ((p:ps),rhs) (drops d k $ Pat ss ms cs)
drops d k pat = pat

pushCase :: Case -> Term -> Term
pushCase (ps,rhs) (Pat ss ms cs) = Pat ss ms ((ps,rhs):cs)
pushCase _        _              = error "unreachable"

ctrOf :: Int -> Term -> (Term, [Term])
ctrOf d Zer     = (Zer           , [])
ctrOf d (Suc p) = (Suc (use d p) , [use d p])
ctrOf d x       = (var d         , [var d])

use :: Int -> Term -> Term
use d (strip -> Var k i) = Var k i 
use d p                  = var d

var :: Int -> Term
var d = Var ("x" ++ show d) d


  -- peel :: [Term] -> [Move] -> [Case] -> PMap -> Term
  -- peel (s:ss) ms (c:cs) pm = peel (s:ss) ms cs (join c pm)
  -- peel ss     ms cs     pm = undefined  

  -- group :: Term -> PatT -> PatT
  -- group c (Pat ss ms ((p:ps):cs)) = case (c,p) of
    -- (Zer , Zer) -> Pat ss ms ((p:ps):cs)
    -- case (c,p) of
      -- (Zer, Zer) -> ((
    -- where ((ss0, ms0, cs0) , (ss1, ms1, cs1)) = group c (Pat ss ms cs)

  -- join :: Case -> PMap -> PMap
  -- join ((Zer   :ps),rhs) ((Zer   ,ks):pm) = (Zer, (ps,rhs) : ks) : pm
  -- join ((Suc x0:ps),rhs) ((Suc x1,ks):pm) = (Suc x0, 
  -- join ((Zer   :ps),rhs) ((x     ,ks):pm)              = (x, ks) : join ((Zer:ps),rhs) pm
  -- join ((Zer   :ps),rhs) []               = [(Zer, [(ps,rhs)])]
  -- join _              _             = undefined















-- type Moves = [Move]

-- -- Convert Pat expression to nested case trees
-- flattenPat :: Int -> [Term] -> Moves -> [([Term], Term)] -> Term
-- flattenPat d scruts moves clauses =
  -- trace ("#flatten:\n" ++ show (Pat scruts moves clauses)) $
  -- case (scruts, clauses) of
    -- ([]  , ([],rhs):ss) -> trace "A" $ flatten rhs
    -- ([]  , _)           -> trace "B" $ Efq
    -- (s:ss, [])          -> trace "C" $ Efq
    -- (s:ss, _)           -> trace "D" $ processColumn d s ss moves (splitColumn clauses)

-- -- Creates the appropriate eliminator based on constructor types
-- processColumn :: Int -> Term -> [Term] -> Moves -> ([Term], [([Term], Term)]) -> Term
-- processColumn d scrut scruts moves (col, rules) 
  -- | all isVar col = trace "all-vars" $ bindVariablesAndContinue d scrut scruts moves col rules
  -- | otherwise     = trace "new-elim" $ makeEliminator d scrut scruts moves col rules

-- bindVariablesAndContinue :: Int -> Term -> [Term] -> Moves -> [Term] -> [([Term], Term)] -> Term
-- bindVariablesAndContinue d scrut scruts moves col rules =
  -- let boundRules = zipWith bindVariable col rules
  -- in flattenPat d scruts moves boundRules
  -- where
    -- bindVariable (Var name _) (restPats, rhs) = (restPats, subst name scrut rhs)
    -- bindVariable (Loc _ term) (restPats, rhs) = bindVariable term (restPats, rhs)
    -- bindVariable _            rule            = rule

-- -- Check if a pattern is a variable
-- isVar :: Term -> Bool
-- isVar (Var _ 0) = True
-- isVar (Loc _ t) = isVar t
-- isVar _         = False

-- -- Build the appropriate eliminator for the column
-- makeEliminator :: Int -> Term -> [Term] -> Moves -> [Term] -> [([Term], Term)] -> Term
-- makeEliminator d scrut scruts moves col rules = result where
    -- result  = applyWithVars moves $ App matcher scrut
    -- matcher = case getCtrType col of
      -- NatT  -> buildSwi d moves col rules scruts
      -- LstT  -> buildMat d moves col rules scruts
      -- BitT  -> buildBif d moves col rules scruts
      -- SigT  -> buildGet d moves col rules scruts
      -- EqlT  -> buildRwt d moves col rules scruts
      -- UniT  -> buildUse d moves col rules scruts
      -- EnuT  -> buildCse d moves col rules scruts
      -- NumT  -> buildNum d moves col rules scruts
      -- _     -> error "Mixed or unknown pattern types"

-- -- Determine constructor type from column
-- data CtrType = NatT | LstT | BitT | SigT | EqlT | UniT | EnuT | NumT | Unknown

-- getCtrType :: [Term] -> CtrType
-- getCtrType []     = Unknown
-- getCtrType (p:ps) = case p of
  -- Zer     -> NatT
  -- Suc _   -> NatT
  -- Nil     -> LstT
  -- Con _ _ -> LstT
  -- Bt0     -> BitT
  -- Bt1     -> BitT
  -- Tup _ _ -> SigT
  -- Rfl     -> EqlT
  -- One     -> UniT
  -- Sym _   -> EnuT
  -- Val _   -> NumT
  -- Loc _ t -> getCtrType (t:ps)
  -- Var _ _ -> getCtrType ps
  -- _       -> Unknown

-- -- Helper to get variable pattern rules with their names
-- getVarPatternRules :: [Term] -> [([Term], Term)] -> [(Name, ([Term], Term))]
-- getVarPatternRules col rules = 
  -- [(nameOf pat, (restPats, rhs)) | (pat, (restPats, rhs)) <- zip col rules, isVar pat]

-- -- Natural Number Eliminator
-- -- -------------------------
-- buildSwi :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildSwi d moves col rules scruts = 
  -- let zerCase = buildCase d moves Zer col rules scruts
      -- sucCase = buildSucCase d moves col rules scruts
  -- in Swi zerCase sucCase

-- buildSucCase :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildSucCase d moves col rules scruts =
  -- let pVar = getFieldVar d 0 (Suc Zer) col
      -- body = buildCase d moves (Suc pVar) col rules (pVar : scruts)
  -- in Lam (nameOf pVar) (\_ -> body)

-- -- List Eliminator
-- -- ---------------
-- buildMat :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildMat d moves col rules scruts = 
  -- let nilCase = buildCase d moves Nil col rules scruts
      -- consCase = buildConsCase d moves col rules scruts
  -- in Mat nilCase consCase

-- buildConsCase :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildConsCase d moves col rules scruts =
  -- let hVar = getFieldVar d 0 (Con Zer Nil) col
      -- tVar = getFieldVar d 1 (Con Zer Nil) col
      -- body = buildCase d moves (Con hVar tVar) col rules (hVar : tVar : scruts)
  -- in Lam (nameOf hVar) (\_ -> Lam (nameOf tVar) (\_ -> body))

-- -- Bit Eliminator
-- -- --------------
-- buildBif :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildBif d moves col rules scruts = 
  -- let falseCase = buildCase d moves Bt0 col rules scruts
      -- trueCase = buildCase d moves Bt1 col rules scruts
  -- in Bif falseCase trueCase

-- -- Pair Eliminator
-- -- ---------------
-- buildGet :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildGet d moves col rules scruts = 
  -- let sigCase = buildTupCase d moves col rules scruts
  -- in Get sigCase

-- buildTupCase :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildTupCase d moves col rules scruts =
  -- let aVar = getFieldVar d 0 (Tup Zer Zer) col
      -- bVar = getFieldVar d 1 (Tup Zer Zer) col
      -- body = buildCase d moves (Tup aVar bVar) col rules (aVar : bVar : scruts)
  -- in Lam (nameOf aVar) (\_ -> Lam (nameOf bVar) (\_ -> body))

-- -- Equality Eliminator
-- -- -------------------
-- buildRwt :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildRwt d moves col rules scruts = 
  -- let rflCase = buildCase d moves Rfl col rules scruts
  -- in Rwt rflCase

-- -- Unit Eliminator
-- -- ----------------
-- buildUse :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildUse d moves col rules scruts = 
  -- let oneCase = buildCase d moves One col rules scruts
  -- in Use oneCase

-- -- Enum Eliminator
-- -- ---------------
-- buildCse :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildCse d moves col rules scruts =
  -- Cse branchCases defaultCase
  -- where
    -- branchCases :: [(String, Term)]
    -- branchCases =
      -- [ (s, buildCase d moves (Sym s) col rules scruts)
      -- | Sym s <- getSymbols col ]

    -- defaultCase :: Term
    -- defaultCase =
      -- wrapWithLam moves $
        -- case getVarPatternRules col rules of
          -- []               -> Lam "WTF"  (\_ -> One)
          -- ((k,(ps,rhs)):_) -> Lam k (\_ -> flattenPat (d + 1) scruts moves [(ps, rhs)])

-- -- Numeric Eliminator
-- -- ------------------
-- buildNum :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildNum d moves col rules scruts = 
  -- -- For now, we create a chain of if-then-else checks for each numeric value
  -- let numVals = getNumericValues col
      -- scrut = head scruts  -- The scrutinee being matched
      -- varRules = getVarPatternRules col rules
      -- defaultCase = case varRules of
        -- [] -> Efq
        -- ((varName, (restPats, rhs)):_) -> 
          -- subst varName scrut (flattenPat d scruts moves [(restPats, rhs)])
  -- in buildNumChain d moves scrut numVals col rules scruts defaultCase

-- -- Build a chain of equality checks for numeric values
-- buildNumChain :: Int -> Moves -> Term -> [Term] -> [Term] -> [([Term], Term)] -> [Term] -> Term -> Term
-- buildNumChain _ _ _ [] _ _ _ defaultCase = defaultCase  -- No matches found, use default
-- buildNumChain d moves scrut (val:vals) col rules scruts defaultCase =
  -- let eqCheck = Op2 EQL scrut val  -- Check if scrutinee equals this value
      -- thenBranch = buildCase d moves val col rules scruts
      -- elseBranch = buildNumChain d moves scrut vals col rules scruts defaultCase
  -- in App (Bif elseBranch thenBranch) eqCheck  -- Apply the boolean eliminator to the equality check

-- -- Get all unique numeric values from a column
-- getNumericValues :: [Term] -> [Term]
-- getNumericValues = uniqueValues . filter isNumericValue where
  -- isNumericValue (Val _)   = True
  -- isNumericValue (Loc _ t) = isNumericValue t
  -- isNumericValue _         = False
  
  -- uniqueValues []             = []
  -- uniqueValues (Loc _ t : xs) = uniqueValues (t : xs)
  -- uniqueValues (Val v   : xs) = Val v : uniqueValues (filter (not . eqVal v) xs)
  -- uniqueValues (_       : xs) = uniqueValues xs
  
  -- eqVal v1 (Val v2)   = v1 == v2
  -- eqVal v1 (Loc _ t)  = eqVal v1 t
  -- eqVal _  _          = False

-- -- Get all unique symbols from a column
-- getSymbols :: [Term] -> [Term]
-- getSymbols = uniqueSymbols . filter isSymbol where

  -- isSymbol (Sym _)   = True
  -- isSymbol (Loc _ t) = isSymbol t
  -- isSymbol _         = False

  -- uniqueSymbols []             = []
  -- uniqueSymbols (Loc _ t : xs) = uniqueSymbols (t : xs)
  -- uniqueSymbols (Sym s   : xs) = Sym s : uniqueSymbols (filter (not . eqSym s) xs)
  -- uniqueSymbols (_       : xs) = uniqueSymbols xs

  -- eqSym s1 (Sym s2)   = s1 == s2
  -- eqSym s1 (Loc _ s2) = eqSym s1 s2
  -- eqSym _  _          = False

-- -- Case Building
-- -- -------------

-- -- Build a single case by specializing rules and wrapping it with `with` lambdas
-- buildCase :: Int -> Moves -> Term -> [Term] -> [([Term], Term)] -> [Term] -> Term
-- buildCase d moves ctr col rules scruts = 
  -- let specialized = specializeRules ctr col rules
      -- core = if null specialized 
             -- then Efq
             -- else flattenPat (d + 1) scruts moves specialized
  -- in wrapWithLam moves core

-- -- Specialize rules for a specific constructor
-- specializeRules :: Term -> [Term] -> [([Term], Term)] -> [([Term], Term)]
-- specializeRules ctr col rules = concat (zipWith spec col rules) where
  -- spec pat (pats, rhs) = case (matches ctr pat, pat) of
    -- (True, Var x 0) -> 
      -- let rhs' = subst x ctr rhs
      -- in [(getFields ctr pat ++ pats, rhs')]
    -- (True, Loc _ (Var x 0)) -> 
      -- let rhs' = subst x ctr rhs
      -- in [(getFields ctr pat ++ pats, rhs')]
    -- (True, _) -> 
      -- [(getFields ctr pat ++ pats, rhs)]
    -- _ -> []

-- -- Check if a pattern matches a constructor
-- matches :: Term -> Term -> Bool
-- matches Zer       Zer       = True
-- matches (Suc _)   (Suc _)   = True
-- matches Nil       Nil       = True
-- matches (Con _ _) (Con _ _) = True
-- matches Bt0       Bt0       = True  
-- matches Bt1       Bt1       = True
-- matches (Tup _ _) (Tup _ _) = True
-- matches Rfl       Rfl       = True
-- matches One       One       = True
-- matches (Sym s1)  (Sym s2)  = s1 == s2
-- matches (Val v1)  (Val v2)  = v1 == v2  -- Numeric values match if equal
-- matches (Loc _ a) b         = matches a b
-- matches a         (Loc _ b) = matches a b
-- matches _         (Var _ 0) = True  -- Variables match anything
-- matches _         _         = False

-- -- Field Extraction
-- -- ----------------

-- getFields :: Term -> Term -> [Term]
-- getFields ctr (Suc n)   = [n]
-- getFields ctr (Con h t) = [h, t]
-- getFields ctr (Tup a b) = [a, b]
-- getFields ctr (Sym _)   = []
-- getFields ctr (Val _)   = []  -- Numeric values have no fields
-- getFields ctr (Var _ 0) = wildcards (ctrArity ctr)
-- getFields ctr (Loc _ t) = getFields ctr t
-- getFields ctr _         = []

-- ctrArity :: Term -> Int
-- ctrArity Zer       = 0
-- ctrArity (Suc _)   = 1
-- ctrArity Nil       = 0
-- ctrArity (Con _ _) = 2
-- ctrArity Bt0       = 0
-- ctrArity Bt1       = 0
-- ctrArity (Tup _ _) = 2
-- ctrArity Rfl       = 0
-- ctrArity One       = 0
-- ctrArity (Sym _)   = 0
-- ctrArity (Val _)   = 0  -- Numeric values have no fields
-- ctrArity (Loc _ t) = ctrArity t
-- ctrArity _         = 0

-- wildcards :: Int -> [Term]
-- wildcards n = replicate n (Var "_" 0)

-- -- Variable Generation
-- -- -------------------

-- getFieldVar :: Int -> Int -> Term -> [Term] -> Term
-- getFieldVar d i ctr col = case findPattern ctr col of
  -- Just pat -> preserveName d i (getFields ctr pat)
  -- Nothing  -> freshVar d i

-- findPattern :: Term -> [Term] -> Maybe Term
-- findPattern ctr = find (matches ctr)

-- preserveName :: Int -> Int -> [Term] -> Term
-- preserveName d i fields = case drop i fields of
  -- ((strip -> Var name 0) : _) -> Var name 0
  -- _                           -> freshVar d i

-- freshVar :: Int -> Int -> Term
-- freshVar d i = Var ("_" ++ show d ++ show i) 0

-- nameOf :: Term -> String
-- nameOf (Var n _) = n
-- nameOf (Loc _ t) = nameOf t
-- nameOf _         = "_"

-- -- Utilities
-- -- ---------

-- splitColumn :: [([Term], Term)] -> ([Term], [([Term], Term)])
-- splitColumn []      = ([], [])
-- splitColumn clauses = unzip [(p, (ps, rhs)) | (p:ps, rhs) <- clauses]

-- -- Helpers for the 'with' list
-- -- ----------------------------

-- -- Wrap term with lambdas for each with variable: λr.λs.body
-- wrapWithLam :: Moves -> Term -> Term
-- wrapWithLam ms t = foldr (\(n,_) b -> Lam n (\_ -> b)) t ms

-- -- Apply with variables to term: term r s
-- applyWithVars :: Moves -> Term -> Term
-- applyWithVars ms t = foldl App t (map (\ (n,_) -> Var n 0) ms)

-- -- Apply with values to term: term F(k) 123
-- applyWithVals :: Moves -> Term -> Term
-- applyWithVals ms t = foldl App t (map snd ms)

-- -- Outer wrapper: creates (λr.λs. ... core) val_r val_s
-- applyToMovedVars :: Moves -> Term -> Term
-- applyToMovedVars ms core = applyWithVals ms (wrapWithLam ms core)

-- -- Helper for variable patterns
-- -- -----------------------------

-- Subst a var for a value in a term
subst :: Name -> Term -> Term -> Term
subst name val term = case term of
  Var k i   -> if k == name && i == 0 then val else term
  Ref k     -> Ref k
  Sub t     -> Sub (subst name val t)
  Fix k f   -> Fix k (\x -> subst name val (f x))
  Let v f   -> Let (subst name val v) (subst name val f)
  Ann x t   -> Ann (subst name val x) (subst name val t)
  Chk x t   -> Chk (subst name val x) (subst name val t)
  Set       -> Set
  Emp       -> Emp
  Efq       -> Efq
  Uni       -> Uni
  One       -> One
  Use f     -> Use (subst name val f)
  Bit       -> Bit
  Bt0       -> Bt0
  Bt1       -> Bt1
  Bif f t   -> Bif (subst name val f) (subst name val t)
  Nat       -> Nat
  Zer       -> Zer
  Suc n     -> Suc (subst name val n)
  Swi z s   -> Swi (subst name val z) (subst name val s)
  Lst t     -> Lst (subst name val t)
  Nil       -> Nil
  Con h t   -> Con (subst name val h) (subst name val t)
  Mat n c   -> Mat (subst name val n) (subst name val c)
  Enu s     -> Enu s
  Sym s     -> Sym s
  Cse c e   -> Cse [(s, subst name val t) | (s, t) <- c] (subst name val e)
  Sig a b   -> Sig (subst name val a) (subst name val b)
  Tup a b   -> Tup (subst name val a) (subst name val b)
  Get f     -> Get (subst name val f)
  All a b   -> All (subst name val a) (subst name val b)
  Lam k f   -> Lam k (\x -> subst name val (f x))
  App f x   -> App (subst name val f) (subst name val x)
  Eql t a b -> Eql (subst name val t) (subst name val a) (subst name val b)
  Rfl       -> Rfl
  Rwt f     -> Rwt (subst name val f)
  Met i t x -> Met i (subst name val t) (map (subst name val) x)
  Ind t     -> Ind (subst name val t)
  Frz t     -> Frz (subst name val t)
  Era       -> Era
  Sup l a b -> Sup l (subst name val a) (subst name val b)
  Num t     -> Num t
  Val v     -> Val v
  Op2 o a b -> Op2 o (subst name val a) (subst name val b)
  Op1 o a   -> Op1 o (subst name val a)
  Pri p     -> Pri p
  Loc s t   -> Loc s (subst name val t)
  Pat s m c -> Pat (map (subst name val) s) m (map substCase c)
    where substCase (pats, rhs) = (map (subst name val) pats, subst name val rhs)







