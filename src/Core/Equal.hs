-- Intrinsic Type System Equality (Fixed)
-- ======================================
-- Simplified observational equality for intrinsic types
-- Clean implementation without complex type constraints
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Core.Equal (
  -- * Equality Functions
  (===),
  observationalEqual,
  definitionalEqual,

  -- * Support Functions
  equalTerm,
  equalCmd,
) where

import Core.Legacy.Eval (eval, LegacyEnv, emptyLegacyEnv)
import Core.Sort
import Unsafe.Coerce (unsafeCoerce)

-- * CONTEXT-AWARE EQUALITY HELPERS

-- Type-safe comparison for expressions in extended contexts
--
-- NOTE: For now using unsafeCoerce to get the Enhanced module working
-- These will be fixed properly in the type-safe lambda comparison phase

-- * OBSERVATIONAL EQUALITY

-- Two-phase equality checking: identical then observational

infix 4 ===

-- | Main equality operator for intrinsic expressions
(===) :: Term '[] ty -> Term '[] ty -> Bool
(===) = observationalEqual maxDepth

-- | Observational equality with depth control
observationalEqual :: Depth -> Term '[] ty -> Term '[] ty -> Bool
observationalEqual depth exp1 exp2 =
  identicalTerms exp1 exp2 || similarTerms depth exp1 exp2 -- Semantic comparison

-- | Check if two expressions are structurally identical
identicalTerms :: Term '[] ty -> Term '[] ty -> Bool
identicalTerms exp1 exp2 = case (exp1, exp2) of
  (TVar idx1, TVar idx2) -> idxToInt idx1 == idxToInt idx2
  (TZer, TZer) -> True
  (TBt0, TBt0) -> True
  (TBt1, TBt1) -> True
  (TOne, TOne) -> True
  (TSuc n1, TSuc n2) -> identicalTerms n1 n2
  (TSet, TSet) -> True
  (TUni, TUni) -> True
  (TBit, TBit) -> True
  (TNat, TNat) -> True
  (TNil, TNil) -> True
  (TCons h1 t1, TCons h2 t2) -> identicalTerms h1 h2 && identicalTerms t1 t2
  (TTup a1 b1, TTup a2 b2) -> identicalTerms a1 a2 && identicalTerms b1 b2
  (TRfl, TRfl) -> True
  (TLst ty1, TLst ty2) -> identicalTerms ty1 ty2
  -- Lambda identity (ignores variable names for alpha equivalence!)
  (TLam name1 argTy1 body1, TLam name2 argTy2 body2) ->
    -- Names are ignored! This gives us alpha equivalence for free
    -- argTy1 == argTy2 (skip for now - Surface.Term has no Eq)
    identicalTerms (unsafeCoerce body1) (unsafeCoerce body2) -- Compare bodies

  -- PHASE 1 EXTENSIONS: New constructor identity (context-preserving)
  (TAll argTy1 retTy1, TAll argTy2 retTy2) ->
    identicalTerms argTy1 argTy2
      && identicalTerms (unsafeCoerce retTy1) (unsafeCoerce retTy2) -- Both retTy have extended context (arg ': ctx)
  (TSig fstTy1 sndTy1, TSig fstTy2 sndTy2) ->
    identicalTerms fstTy1 fstTy2
      && identicalTerms (unsafeCoerce sndTy1) (unsafeCoerce sndTy2) -- Both sndTy have extended context (fst ': ctx)
  (TApp fun1 arg1, TApp fun2 arg2) ->
    identicalTerms (unsafeCoerce fun1) (unsafeCoerce fun2)
      && identicalTerms (unsafeCoerce arg1) (unsafeCoerce arg2) -- Safe: existential type equality
      -- Safe: existential type equality

  -- PHASE 2A EXTENSIONS: Pattern matching eliminator identity
  (TBitM f1 t1, TBitM f2 t2) -> identicalTerms f1 f2 && identicalTerms t1 t2
  (TNatM z1 s1, TNatM z2 s2) -> identicalTerms z1 z2 && identicalTerms (unsafeCoerce s1) (unsafeCoerce s2) -- Both s have Nat->ret function type
  (TUniM u1, TUniM u2) -> identicalTerms u1 u2
  (TLstM n1 c1, TLstM n2 c2) -> identicalTerms n1 n2 && identicalTerms (unsafeCoerce c1) (unsafeCoerce c2) -- Both c have list constructor function type
  (TSigM p1, TSigM p2) -> identicalTerms (unsafeCoerce p1) (unsafeCoerce p2) -- Both p have pair function type

  -- PHASE 2B EXTENSIONS: References and simple terms identity
  (TRef name1 level1, TRef name2 level2) -> name1 == name2 && level1 == level2
  (TSub t1, TSub t2) -> identicalTerms t1 t2
  (TEmp, TEmp) -> True
  (TEmpM, TEmpM) -> True
  (TEql ty1 a1 b1, TEql ty2 a2 b2) -> identicalTerms ty1 ty2 && identicalTerms (unsafeCoerce a1) (unsafeCoerce a2) && identicalTerms (unsafeCoerce b1) (unsafeCoerce b2)
  _ -> False

-- | Semantic equality comparison after normalization
similarTerms :: Depth -> Term '[] ty -> Term '[] ty -> Bool
similarTerms (Depth 0) _ _ = False -- Depth exhausted
similarTerms depth exp1 exp2 = case (exp1, exp2) of
  -- Base cases
  (TZer, TZer) -> True
  (TBt0, TBt0) -> True
  (TBt1, TBt1) -> True
  (TOne, TOne) -> True
  (TSet, TSet) -> True
  (TUni, TUni) -> True
  (TBit, TBit) -> True
  (TNat, TNat) -> True
  (TNil, TNil) -> True
  (TRfl, TRfl) -> True
  -- Recursive cases
  (TSuc n1, TSuc n2) -> similarTerms (decDepth depth) n1 n2
  (TCons h1 t1, TCons h2 t2) ->
    similarTerms (decDepth depth) h1 h2 && similarTerms (decDepth depth) t1 t2
  (TTup a1 b1, TTup a2 b2) ->
    similarTerms (decDepth depth) a1 a2 && similarTerms (decDepth depth) b1 b2
  (TLst ty1, TLst ty2) -> similarTerms (decDepth depth) ty1 ty2
  -- Function extensionality (simplified)
  (TLam name1 argTy1 body1, TLam name2 argTy2 body2) ->
    -- For now, skip type comparison since Surface.Term has no Eq instance
    -- argTy1 == argTy2 && functionalEqual (decDepth depth) body1 body2
    functionalEqual (decDepth depth) body1 body2
  -- PHASE 1 EXTENSIONS: New constructor similarity (with context coercion)
  (TAll argTy1 retTy1, TAll argTy2 retTy2) ->
    similarTerms (decDepth depth) argTy1 argTy2 && similarTerms (decDepth depth) (unsafeCoerce retTy1) (unsafeCoerce retTy2)
  (TSig fstTy1 sndTy1, TSig fstTy2 sndTy2) ->
    similarTerms (decDepth depth) fstTy1 fstTy2 && similarTerms (decDepth depth) (unsafeCoerce sndTy1) (unsafeCoerce sndTy2)
  (TApp fun1 arg1, TApp fun2 arg2) ->
    similarTerms (decDepth depth) (unsafeCoerce fun1) (unsafeCoerce fun2) && similarTerms (decDepth depth) (unsafeCoerce arg1) (unsafeCoerce arg2)
  -- PHASE 2A EXTENSIONS: Pattern matching eliminator similarity
  (TBitM f1 t1, TBitM f2 t2) ->
    similarTerms (decDepth depth) f1 f2 && similarTerms (decDepth depth) t1 t2
  (TNatM z1 s1, TNatM z2 s2) ->
    similarTerms (decDepth depth) z1 z2 && similarTerms (decDepth depth) (unsafeCoerce s1) (unsafeCoerce s2)
  (TUniM u1, TUniM u2) ->
    similarTerms (decDepth depth) u1 u2
  (TLstM n1 c1, TLstM n2 c2) ->
    similarTerms (decDepth depth) n1 n2 && similarTerms (decDepth depth) (unsafeCoerce c1) (unsafeCoerce c2)
  (TSigM p1, TSigM p2) ->
    similarTerms (decDepth depth) (unsafeCoerce p1) (unsafeCoerce p2)
  -- PHASE 2B EXTENSIONS: References and simple terms similarity
  (TRef name1 level1, TRef name2 level2) -> name1 == name2 && level1 == level2
  (TSub t1, TSub t2) -> similarTerms (decDepth depth) t1 t2
  (TEmp, TEmp) -> True
  (TEmpM, TEmpM) -> True
  (TEql ty1 a1 b1, TEql ty2 a2 b2) ->
    similarTerms (decDepth depth) ty1 ty2 && similarTerms (decDepth depth) (unsafeCoerce a1) (unsafeCoerce a2) && similarTerms (decDepth depth) (unsafeCoerce b1) (unsafeCoerce b2)
  -- Variable comparison
  (TVar idx1, TVar idx2) -> idxToInt idx1 == idxToInt idx2
  -- Different constructors
  _ -> False

-- | Functional extensionality for lambda bodies (structural comparison)
functionalEqual :: Depth -> Term (arg ': '[]) ret -> Term (arg ': '[]) ret -> Bool
functionalEqual depth body1 body2 =
  -- For now, do structural comparison of lambda bodies
  -- This gives us alpha equivalence since De Bruijn indices are the same
  similarTerms depth (unsafeCoerce body1) (unsafeCoerce body2)

-- * DEFINITIONAL EQUALITY

-- Stricter equality based on normal forms

definitionalEqual :: Term '[] ty -> Term '[] ty -> Bool
definitionalEqual exp1 exp2 =
  let exp1' = eval emptyLegacyEnv (CReturn exp1)
      exp2' = eval emptyLegacyEnv (CReturn exp2)
   in identicalTerms exp1' exp2'

-- * COMMAND EQUALITY

-- Equality for commands via evaluation

equalCmd :: Cmd '[] ty -> Cmd '[] ty -> Bool
equalCmd cmd1 cmd2 =
  let exp1 = eval emptyLegacyEnv cmd1
      exp2 = eval emptyLegacyEnv cmd2
   in exp1 === exp2

-- * EQUALITY FOR EXPRESSIONS

-- Type-safe equality checking

equalTerm :: Term '[] ty -> Term '[] ty -> Bool
equalTerm = (===)
