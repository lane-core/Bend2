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

import Core.Type
import Data.List (nub, find)
import qualified Data.Map as M

-- Main Flattener
-- --------------

flatten :: Term -> Term
flatten (Var n i)      = Var n i
flatten (Ref n)        = Ref n
flatten (Sub t)        = Sub (flatten t)
flatten (Fix n f)      = Fix n (\x -> flatten (f x))
flatten (Let v f)      = Let (flatten v) (flatten f)
flatten Set            = Set
flatten (Ann x t)      = Ann (flatten x) (flatten t)
flatten (Chk x t)      = Chk (flatten x) (flatten t)
flatten Emp            = Emp
flatten Efq            = Efq
flatten Uni            = Uni
flatten One            = One
flatten (Use f)        = Use (flatten f)
flatten Bit            = Bit
flatten Bt0            = Bt0
flatten Bt1            = Bt1
flatten (Bif f t)      = Bif (flatten f) (flatten t)
flatten Nat            = Nat
flatten Zer            = Zer
flatten (Suc n)        = Suc (flatten n)
flatten (Swi z s)      = Swi (flatten z) (flatten s)
flatten (Lst t)        = Lst (flatten t)
flatten Nil            = Nil
flatten (Con h t)      = Con (flatten h) (flatten t)
flatten (Mat n c)      = Mat (flatten n) (flatten c)
flatten (Enu s)        = Enu s
flatten (Sym s)        = Sym s
flatten (Cse c)        = Cse [(s, flatten t) | (s, t) <- c]
flatten (Sig a b)      = Sig (flatten a) (flatten b)
flatten (Tup a b)      = Tup (flatten a) (flatten b)
flatten (Get f)        = Get (flatten f)
flatten (All a b)      = All (flatten a) (flatten b)
flatten (Lam n f)      = Lam n (\x -> flatten (f x))
flatten (App f x)      = App (flatten f) (flatten x)
flatten (Eql t a b)    = Eql (flatten t) (flatten a) (flatten b)
flatten Rfl            = Rfl
flatten (Rwt f)        = Rwt (flatten f)
flatten (Met i t xs)   = Met i (flatten t) (map flatten xs)
flatten (Ind t)        = Ind (flatten t)
flatten (Frz t)        = Frz (flatten t)
flatten Era            = Era
flatten (Sup l a b)    = Sup l (flatten a) (flatten b)
flatten (Loc s t)      = Loc s (flatten t)
flatten (Pat s m c)    = wrapLamApplyVals m (flattenPat 0 s m c)

flattenBook :: Book -> Book
flattenBook (Book defs) = Book (M.map flattenDefn defs)
  where flattenDefn (term, typ) = (flatten term, flatten typ)

-- Pattern Match Flattening
-- ------------------------

type Moves = [Move]

-- Convert Pat expression to nested case trees
flattenPat :: Int -> [Term] -> Moves -> [([Term], Term)] -> Term
flattenPat d scruts moves clauses = case (scruts, clauses) of
  ([]  , [([], rhs)]) -> flatten rhs -- Base case: RHS is wrapped by buildCase
  ([]  , a)           -> Efq
  (s:ss, [])          -> Efq
  (s:ss, _)           -> processColumn d s ss moves (splitColumn clauses)

-- Process a single column of patterns
-- Creates the appropriate eliminator based on constructor types
processColumn :: Int -> Term -> [Term] -> Moves -> ([Term], [([Term], Term)]) -> Term
processColumn d scrut scruts moves (col, rules) 
  | allVars col = flattenPat d scruts moves rules
  | otherwise   = buildEliminator d scrut scruts moves col rules

-- -- Handle the case where all patterns in a column are variables
-- -- We need to bind each variable to the scrutinee and continue
-- bindVariablesAndContinue :: Int -> Term -> [Term] -> Moves -> [Term] -> [([Term], Term)] -> Term
-- bindVariablesAndContinue d scrut scruts moves col rules = 
  -- let boundRules = zipWith bindVariable col rules
  -- in flattenPat d scruts moves boundRules
  -- where
    -- -- Bind a variable pattern to the scrutinee in the RHS
    -- bindVariable :: Term -> ([Term], Term) -> ([Term], Term)
    -- bindVariable (Var name _) (restPats, rhs) = (restPats, Let scrut (Lam name (\_ -> rhs)))
    -- bindVariable _ rule = rule -- This shouldn't happen if allVars is true

-- Check if all patterns in column are variables
allVars :: [Term] -> Bool
allVars = all isVar

-- Check if a pattern is a variable
isVar :: Term -> Bool
isVar (Var _ 0) = True
isVar (Loc _ t) = isVar t
isVar _         = False

-- Build the appropriate eliminator for the column
buildEliminator :: Int -> Term -> [Term] -> Moves -> [Term] -> [([Term], Term)] -> Term
buildEliminator d scrut scruts moves col rules = 
  let builder = case getCtrType col of
        NatT  -> buildSwi  d moves col rules scruts
        LstT  -> buildMat  d moves col rules scruts
        BitT  -> buildBif  d moves col rules scruts
        SigT  -> buildGet  d moves col rules scruts
        EqlT  -> buildRwt  d moves col rules scruts
        UniT  -> buildUse  d moves col rules scruts
        EnuT  -> buildCse  d moves col rules scruts
        _     -> error "Mixed or unknown pattern types"
      -- Every eliminator is applied to its scrutinee, then to all `with` variables.
      base = App builder scrut
  in applyWithVars moves base

-- Determine constructor type from column
data CtrType = NatT | LstT | BitT | SigT | EqlT | UniT | EnuT | Unknown

getCtrType :: [Term] -> CtrType
getCtrType []    = Unknown
getCtrType (p:ps) = case p of
  Zer     -> NatT
  Suc _   -> NatT
  Nil     -> LstT
  Con _ _ -> LstT
  Bt0     -> BitT
  Bt1     -> BitT
  Tup _ _ -> SigT
  Rfl     -> EqlT
  One     -> UniT
  Sym _   -> EnuT
  Loc _ t -> getCtrType (t:ps)
  Var _ _ -> getCtrType ps
  _       -> Unknown

-- Natural Number Eliminator
-- -------------------------
buildSwi :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildSwi d moves col rules scruts = Swi zerCase sucCase where
  zerCase = buildCase d moves Zer col rules scruts
  sucCase = buildSucCase d moves col rules scruts

buildSucCase :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildSucCase d moves col rules scruts = 
  let var  = getFieldVar d 0 (Suc Zer) col
      body = buildCase d moves (Suc var) col rules (var : scruts)
  in Lam (nameOf var) (\_ -> body)

-- List Eliminator
-- ---------------
buildMat :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildMat d moves col rules scruts = Mat nilCase consCase where
  nilCase  = buildCase d moves Nil col rules scruts
  consCase = buildConsCase d moves col rules scruts

buildConsCase :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildConsCase d moves col rules scruts =
  let hVar = getFieldVar d 0 (Con Zer Nil) col
      tVar = getFieldVar d 1 (Con Zer Nil) col
      body = buildCase d moves (Con hVar tVar) col rules (hVar : tVar : scruts)
  in Lam (nameOf hVar) (\_ -> Lam (nameOf tVar) (\_ -> body))

-- Bit Eliminator
-- --------------
buildBif :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildBif d moves col rules scruts = Bif falseCase trueCase where
  falseCase = buildCase d moves Bt0 col rules scruts
  trueCase  = buildCase d moves Bt1 col rules scruts

-- Pair Eliminator
-- ---------------
buildGet :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildGet d moves col rules scruts = Get sigCase where
  sigCase = buildTupCase d moves col rules scruts

buildTupCase :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildTupCase d moves col rules scruts =
  let aVar = getFieldVar d 0 (Tup Zer Zer) col
      bVar = getFieldVar d 1 (Tup Zer Zer) col
      body = buildCase d moves (Tup aVar bVar) col rules (aVar : bVar : scruts)
  in Lam (nameOf aVar) (\_ -> Lam (nameOf bVar) (\_ -> body))

-- Equality Eliminator
-- -------------------
buildRwt :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildRwt d moves col rules scruts = Rwt rflCase where
  rflCase = buildCase d moves Rfl col rules scruts

-- Unit Eliminator
-- ----------------
buildUse :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildUse d moves col rules scruts = Use oneCase where
  oneCase = buildCase d moves One col rules scruts

-- Enum Eliminator
-- ---------------
buildCse :: Int -> Moves -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildCse d moves col rules scruts = Cse cases where
  cases = [(s, buildCase d moves (Sym s) col rules scruts) | Sym s <- getSymbols col]

-- Get all unique symbols from a column
getSymbols :: [Term] -> [Term]
getSymbols = uniqueSymbols . filter isSymbol where

  isSymbol (Sym _)   = True
  isSymbol (Loc _ t) = isSymbol t
  isSymbol _         = False

  uniqueSymbols []             = []
  uniqueSymbols (Loc _ t : xs) = uniqueSymbols (t : xs)
  uniqueSymbols (Sym s   : xs) = Sym s : uniqueSymbols (filter (not . eqSym s) xs)
  uniqueSymbols (_       : xs) = uniqueSymbols xs

  eqSym s1 (Sym s2)   = s1 == s2
  eqSym s1 (Loc _ s2) = eqSym s1 s2
  eqSym _  _          = False

-- Case Building
-- -------------

-- Build a single case by specializing rules and wrapping it with `with` lambdas
buildCase :: Int -> Moves -> Term -> [Term] -> [([Term], Term)] -> [Term] -> Term
buildCase d moves ctr col rules scruts = 
  let specialized = specializeRules ctr col rules
      core = if null specialized 
             then Efq
             else flattenPat (d + 1) scruts moves specialized
  in wrapWithLam moves core

-- Specialize rules for a specific constructor
specializeRules :: Term -> [Term] -> [([Term], Term)] -> [([Term], Term)]
specializeRules ctr col rules = concat (zipWith spec col rules) where
  spec pat (pats, rhs) = case (matches ctr pat, getFields ctr pat) of
    -- (True, fields) -> [(fields ++ pats, bindVariableIfNeeded ctr pat rhs)]
    (True, fields) -> [(fields ++ pats, rhs)]
    _              -> []

-- -- Bind variable to constructor if the pattern is a variable
-- bindVariableIfNeeded :: Term -> Term -> Term -> Term
-- bindVariableIfNeeded ctr (Var name 0) rhs = Let ctr (Lam name (\_ -> rhs))
-- bindVariableIfNeeded _ _ rhs = rhs


-- Check if a pattern matches a constructor
matches :: Term -> Term -> Bool
matches Zer       Zer       = True
matches (Suc _)   (Suc _)   = True
matches Nil       Nil       = True
matches (Con _ _) (Con _ _) = True
matches Bt0       Bt0       = True  
matches Bt1       Bt1       = True
matches (Tup _ _) (Tup _ _) = True
matches Rfl       Rfl       = True
matches One       One       = True
matches (Sym s1)  (Sym s2)  = s1 == s2
matches (Loc _ a) b         = matches a b
matches a         (Loc _ b) = matches a b
matches _         (Var _ 0) = True  -- Variables match anything
matches _         _         = False

-- Field Extraction
-- ----------------

getFields :: Term -> Term -> [Term]
getFields ctr (Suc n)   = [n]
getFields ctr (Con h t) = [h, t]
getFields ctr (Tup a b) = [a, b]
getFields ctr (Sym _)   = []
getFields ctr (Var _ 0) = wildcards (ctrArity ctr)
getFields ctx (Loc _ t) = getFields ctx t
getFields ctr _         = []

ctrArity :: Term -> Int
ctrArity Zer       = 0
ctrArity (Suc _)   = 1
ctrArity Nil       = 0
ctrArity (Con _ _) = 2
ctrArity Bt0       = 0
ctrArity Bt1       = 0
ctrArity (Tup _ _) = 2
ctrArity Rfl       = 0
ctrArity One       = 0
ctrArity (Sym _)   = 0
ctrArity (Loc _ t) = ctrArity t
ctrArity _         = 0

wildcards :: Int -> [Term]
wildcards n = replicate n (Var "_" 0)

-- Variable Generation
-- -------------------

getFieldVar :: Int -> Int -> Term -> [Term] -> Term
getFieldVar d i ctr col = case findPattern ctr col of
  Just pat -> preserveName d i (getFields ctr pat)
  Nothing  -> freshVar d i

findPattern :: Term -> [Term] -> Maybe Term
findPattern ctr = find (matches ctr)

preserveName :: Int -> Int -> [Term] -> Term
preserveName d i fields = case drop i fields of
  ((strip -> Var name 0) : _) -> Var name 0
  _                           -> freshVar d i

freshVar :: Int -> Int -> Term
freshVar d i = Var ("_p" ++ show d ++ show i) 0

nameOf :: Term -> String
nameOf (Var n _) = n
nameOf (Loc _ t) = nameOf t
nameOf _         = "_"

-- Utilities
-- ---------

splitColumn :: [([Term], Term)] -> ([Term], [([Term], Term)])
splitColumn []      = ([], [])
splitColumn clauses = unzip [(p, (ps, rhs)) | (p:ps, rhs) <- clauses]

-- Helpers for the 'with' list
-- ----------------------------

-- Wrap term with lambdas for each with variable: λr.λs.body
wrapWithLam :: Moves -> Term -> Term
wrapWithLam ms t = foldr (\(n,_) b -> Lam n (\_ -> b)) t ms

-- Apply with variables to term: term r s
applyWithVars :: Moves -> Term -> Term
applyWithVars ms t = foldl App t (map (\ (n,_) -> Var n 0) ms)

-- Apply with values to term: term F(k) 123
applyWithVals :: Moves -> Term -> Term
applyWithVals ms t = foldl App t (map snd ms)

-- Outer wrapper: creates (λr.λs. ... core) val_r val_s
wrapLamApplyVals :: Moves -> Term -> Term
wrapLamApplyVals ms core = applyWithVals ms (wrapWithLam ms core)
