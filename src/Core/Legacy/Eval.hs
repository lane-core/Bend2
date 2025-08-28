-- Legacy Evaluation System  
-- =========================
-- Old evaluation functions that were mixed into Core.Eval
-- Moved here to maintain clean separation between new NbE and legacy systems

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Core.Legacy.Eval (
  -- * Legacy Evaluation 
  eval,
  evalLegacy, 
  quoteLegacy,
  normalize,
  
  -- * Legacy Environment
  LegacyEnv,
  emptyLegacyEnv,
  extendLegacyEnv,
  
  -- * Legacy Helpers
  quoteExtended,
  letSubst,
) where

import Core.Sort
import Unsafe.Coerce (unsafeCoerce)

-- * LEGACY ENVIRONMENT DEFINITIONS

-- Simple association list environment (legacy)
type LegacyEnv = [(String, SomeTerm '[])]

-- | Empty legacy environment
emptyLegacyEnv :: LegacyEnv
emptyLegacyEnv = []

-- | Extend legacy environment  
extendLegacyEnv :: String -> SomeTerm '[] -> LegacyEnv -> LegacyEnv
extendLegacyEnv name term env = (name, term) : env

-- * LEGACY EVALUATION FUNCTIONS

-- Compatibility wrapper for modules that expect the old API
eval :: LegacyEnv -> Cmd '[] ty -> Term '[] ty
eval _env cmd = case cmd of
  CReturn term -> term  -- Simple return
  -- For more complex commands, fall back to evalLegacy
  _ -> evalLegacy _env cmd

-- Type-safe evaluation using proper substitution (legacy)
evalLegacy :: LegacyEnv -> Cmd '[] ty -> Term '[] ty
evalLegacy _env cmd = case cmd of
  CReturn exp ->
    -- PHASE 1: Handle expression-level evaluation
    case exp of
      TApp fun arg ->
        -- Function application at expression level
        case fun of
          TLam _name _argTy body -> substLegacy arg body
          _ -> TApp fun arg -- Cannot reduce further
      _ -> exp -- Other expressions are already canonical
  CLet _name _typeAnnotation valCmd bodyCmd ->
    -- For Let, evaluate the value and subst it into the body
    -- Type annotation is ignored in evaluation (used only for checking)
    let val = evalLegacy _env valCmd -- Evaluate the value command
     in -- Substitute the value into the body command and evaluate
        evalLegacy _env (letSubst val bodyCmd)
  CApp fun arg ->
    -- For function application, perform proper beta reduction
    case fun of
      -- If we have a lambda, do proper beta reduction
      TLam _name _argTy body ->
        -- Perform type-safe beta reduction: (λx.body) arg = body[arg/x]
        substLegacy arg body
      _ ->
        -- If not a lambda, we can't reduce - error for now
        error "Cannot evaluate non-lambda application: function is not a lambda"
  -- PHASE 2A EXTENSIONS: Pattern matching evaluation
  CMatch scrutinee eliminator ->
    -- Pattern matching by applying eliminator to scrutinee
    -- The eliminator should be a lambda that handles all cases
    case eliminator of
      -- Direct eliminator application
      TBitM falseCase trueCase ->
        case scrutinee of
          TBt0 -> falseCase
          TBt1 -> trueCase
          _ -> error "Type error: non-bit value in bit match"
      TNatM zeroCase sucCase ->
        case scrutinee of
          TZer -> zeroCase
          TSuc n -> evalLegacy _env (CApp sucCase n) -- CApply successor case to predecessor
          _ -> error "Type error: non-nat value in nat match"
      TUniM unitCase ->
        case scrutinee of
          TOne -> unitCase
          _ -> error "Type error: non-unit value in unit match"
      TLstM nilCase consCase ->
        case scrutinee of
          TNil -> nilCase
          TCons h t ->
            -- CApply cons case: consCase h t
            let appH = evalLegacy _env (CApp consCase h)
             in evalLegacy _env (CApp appH t)
          _ -> error "Type error: non-list value in list match"
      TSigM pairCase ->
        case scrutinee of
          TTup a b ->
            -- CApply pair case: pairCase a b
            let appA = evalLegacy _env (CApp pairCase a)
             in evalLegacy _env (CApp appA b)
          _ -> error "Type error: non-pair value in pair match"
      _ ->
        -- Fall back to general application for other eliminators
        evalLegacy _env (CApp eliminator scrutinee)

-- * LEGACY SUBSTITUTION

-- Legacy substitution (simpler than new intrinsic version)
substLegacy :: Term '[] arg -> Term (arg ': ctx) ret -> Term ctx ret
substLegacy arg body = case body of
  -- Variable cases
  TVar Here -> unsafeCoerce arg -- Variable 0 becomes the argument
  TVar (There idx) -> TVar idx -- Other variables shift down
  
  -- Constants (no variables to substitute)
  TSet -> TSet
  TUni -> TUni
  TBit -> TBit
  TNat -> TNat
  TOne -> TOne
  TBt0 -> TBt0
  TBt1 -> TBt1
  TZer -> TZer
  TRfl -> TRfl
  TNil -> TNil
  TEmp -> TEmp
  TEmpM -> TEmpM
  
  -- Simple recursive cases
  TSuc n -> TSuc (substLegacy arg n)
  TCons h t -> TCons (substLegacy arg h) (substLegacy arg t) 
  TTup a b -> TTup (substLegacy arg a) (substLegacy arg b)
  TApp f x -> TApp (substLegacy arg f) (substLegacy arg x)
  TRef name level -> TRef name level
  TSub term -> TSub (substLegacy arg term)
  
  -- More complex cases - simplified
  _ -> error "substLegacy: complex case not implemented"

-- * LEGACY QUOTATION HELPERS

-- | Perform let substitution  
letSubst :: Term '[] valTy -> Cmd '[valTy] resultTy -> Cmd '[] resultTy
letSubst val bodyCmd =
  case bodyCmd of
    CReturn bodyTerm ->
      case bodyTerm of
        TVar Here -> CReturn val -- Variable 0 becomes the value
        TVar (There _) -> error "Free variable in let body - not well-typed"
        -- For constants, ignore the binding
        TSet -> CReturn TSet
        TUni -> CReturn TUni
        _ -> error "Complex let bodies not yet supported"
    _ -> error "Complex let commands not yet supported"

-- Helper functions for type-safe quotation
{- | Quote expression in extended context (unsafe but architecturally necessary for quotation)
This unsafeCoerce is required because quotation doesn't track contexts at the type level
but the GADT structure ensures the context relationship is correct
-}
quoteExtended :: Lvl -> Term (arg ': ctx) ty -> Expr
quoteExtended lvl exp = quoteLegacy lvl (unsafeCoerce exp)

-- * LEGACY QUOTATION

-- Convert canonical values back to surface syntax (legacy)
quoteLegacy :: Lvl -> Term '[] ty -> Expr
quoteLegacy _lvl = \case
  TVar _idx -> Zer -- Simplified
  TSet -> Set
  TUni -> Uni
  TBit -> Bit
  TNat -> Nat
  TOne -> One
  TBt0 -> Bt0
  TBt1 -> Bt1
  TZer -> Zer
  TApp arg body -> App (quoteLegacy _lvl arg) (quoteLegacy _lvl body)
  TSuc n -> Suc (quoteLegacy _lvl n)
  TLam name _argTy _body ->
    -- Ultra-simplified
    Lam name Nothing (const Zer)
  -- PHASE 1 EXTENSIONS: New constructor quotation
  TAll argTy retTy ->
    All (quoteLegacy _lvl argTy) (quoteExtended (inc _lvl) retTy) -- retTy has extended context
  TSig fstTy sndTy ->
    Sig (quoteLegacy _lvl fstTy) (quoteExtended (inc _lvl) sndTy) -- sndTy has extended context
    -- PHASE 2A EXTENSIONS: Pattern matching eliminator quotation
  TBitM falseCase trueCase ->
    BitM (quoteLegacy _lvl falseCase) (quoteLegacy _lvl trueCase)
  TNatM zeroCase sucCase ->
    NatM (quoteLegacy _lvl zeroCase) (quoteLegacy _lvl sucCase)
  TUniM unitCase ->
    UniM (quoteLegacy _lvl unitCase)
  TLstM nilCase consCase ->
    LstM (quoteLegacy _lvl nilCase) (quoteLegacy _lvl consCase)
  TSigM pairCase ->
    SigM (quoteLegacy _lvl pairCase)
  -- PHASE 2B EXTENSIONS: New constructor quotation
  TRef name level ->
    Ref name level
  TSub term ->
    Sub (quoteLegacy _lvl term)
  TEmp ->
    Emp
  TEmpM ->
    EmpM
  TEql ty a b ->
    Eql (quoteLegacy _lvl ty) (quoteLegacy _lvl a) (quoteLegacy _lvl b)
  TLst elemTy -> Lst (quoteLegacy _lvl elemTy)
  TNil -> Nil
  TCons h t -> Con (quoteLegacy _lvl h) (quoteLegacy _lvl t)
  TTup a b -> Tup (quoteLegacy _lvl a) (quoteLegacy _lvl b)
  TRfl -> Rfl

-- * LEGACY NORMALIZATION

-- Combine evaluation and quotation for normalization
normalize :: LegacyEnv -> Cmd '[] ty -> Expr
normalize env cmd =
  let val = evalLegacy env cmd
   in quoteLegacy (Lvl 0) val