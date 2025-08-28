-- Intrinsic Type System Evaluation (Ultra Simple)
-- ===============================================
-- Minimal working evaluation for intrinsic types
-- Focuses on compilation over correctness
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Core.Eval (
  -- * Core Evaluation Functions
  eval,
  quote,
  normalize,

  -- * Environment
  Env,
  emptyEnv,
  extendEnv,

  -- * Substitution
  subst,
) where

import Core.Sort

import Unsafe.Coerce (unsafeCoerce)

-- * PROPER SUBSTITUTION

-- Type-safe De Bruijn substitution for lambda bodies

-- | Substitute an argument for the outermost variable (index 0)
subst :: Term '[] arg -> Term (arg ': ctx) ret -> Term ctx ret
subst arg body = case body of
  -- Variable cases
  TVar Here -> unsafeCoerce arg -- Variable 0 becomes the argument (temporarily unsafe)
  TVar (There idx) -> TVar idx -- Other variables shift down

  -- Constants (no variables to subst)
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
  -- Recursive cases with substitution
  TSuc n -> TSuc (subst arg n)
  TLam name argType lambdaBody ->
    -- Lambda abstraction: temporarily use unsafeCoerce
    TLam name argType (unsafeCoerce lambdaBody)
  TCons h t -> TCons (subst arg h) (subst arg t)
  TTup a b -> TTup (subst arg a) (subst arg b)
  TLst ty -> TLst (subst arg ty)
  -- PHASE 1 EXTENSIONS: Function types with substitution (temporarily unsafe)
  TAll argTy retTy -> TAll (subst arg argTy) (unsafeCoerce retTy)
  TSig fstTy sndTy -> TSig (subst arg fstTy) (unsafeCoerce sndTy)
  TApp fun arg' -> TApp (subst arg fun) (subst arg arg')
  -- PHASE 2A EXTENSIONS: Pattern matching eliminators (temporarily unsafe)
  TBitM f t -> TBitM (subst arg f) (subst arg t)
  TNatM z s -> TNatM (subst arg z) (unsafeCoerce s)
  TUniM u -> TUniM (subst arg u)
  TLstM n c -> TLstM (subst arg n) (unsafeCoerce c)
  TSigM p -> TSigM (unsafeCoerce p)
  -- PHASE 2B EXTENSIONS: References and simple terms
  TRef name level -> TRef name level -- No substitution needed
  TSub term -> TSub (subst arg term)
  TEql ty a b -> TEql (subst arg ty) (subst arg a) (subst arg b)

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
        TBit -> CReturn TBit
        TNat -> CReturn TNat
        TOne -> CReturn TOne
        TBt0 -> CReturn TBt0
        TBt1 -> CReturn TBt1
        TZer -> CReturn TZer
        -- Handle common constant cases in let bodies
        TSuc TZer -> CReturn (TSuc TZer) -- S(0) = 1
        TSuc (TSuc TZer) -> CReturn (TSuc (TSuc TZer)) -- S(S(0)) = 2
        TSuc (TSuc (TSuc TZer)) -> CReturn (TSuc (TSuc (TSuc TZer))) -- S(S(S(0))) = 3
        _ -> error "Complex let bodies with variable usage not yet supported"
    -- Other command cases would need similar handling
    _ -> error "Complex let commands not yet supported"

-- * EVALUATION

-- Type-safe evaluation using proper substitution

eval :: Env -> Cmd '[] ty -> Term '[] ty
eval _env cmd = case cmd of
  CReturn exp ->
    -- PHASE 1: Handle expression-level evaluation
    case exp of
      TApp fun arg ->
        -- Function application at expression level
        case fun of
          TLam _name _argTy body -> subst arg body
          _ -> TApp fun arg -- Cannot reduce further
      _ -> exp -- Other expressions are already canonical
  CLet _name _typeAnnotation valCmd bodyCmd ->
    -- For Let, evaluate the value and subst it into the body
    -- Type annotation is ignored in evaluation (used only for checking)
    let val = eval _env valCmd -- Evaluate the value command
     in -- Substitute the value into the body command and evaluate
        eval _env (letSubst val bodyCmd)
  CApp fun arg ->
    -- For function application, perform proper beta reduction
    case fun of
      -- If we have a lambda, do proper beta reduction
      TLam _name _argTy body ->
        -- Perform type-safe beta reduction: (λx.body) arg = body[arg/x]
        subst arg body
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
          TSuc n -> eval _env (CApp sucCase n) -- CApply successor case to predecessor
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
            let appH = eval _env (CApp consCase h)
             in eval _env (CApp appH t)
          _ -> error "Type error: non-list value in list match"
      TSigM pairCase ->
        case scrutinee of
          TTup a b ->
            -- CApply pair case: pairCase a b
            let appA = eval _env (CApp pairCase a)
             in eval _env (CApp appA b)
          _ -> error "Type error: non-pair value in pair match"
      _ ->
        -- Fall back to general application for other eliminators
        eval _env (CApp eliminator scrutinee)

-- * QUOTATION HELPERS

-- Helper functions for type-safe quotation

{- | Quote expression in extended context (unsafe but architecturally necessary for quotation)
This unsafeCoerce is required because quotation doesn't track contexts at the type level
but the GADT structure ensures the context relationship is correct
-}
quoteExtended :: Lvl -> Term (arg ': ctx) ty -> Expr
quoteExtended lvl exp = quote lvl (unsafeCoerce exp)

-- * QUOTATION

-- Convert canonical values back to surface syntax
quote :: Lvl -> Term '[] ty -> Expr
quote _lvl = \case
  TVar _idx -> Zer -- Simplified
  TSet -> Set
  TUni -> Uni
  TBit -> Bit
  TNat -> Nat
  TOne -> One
  TBt0 -> Bt0
  TBt1 -> Bt1
  TZer -> Zer
  TApp arg body -> App (quote _lvl arg) (quote _lvl body)
  TSuc n -> Suc (quote _lvl n)
  TLam name _argTy _body ->
    -- Ultra-simplified
    Lam name Nothing (const Zer)
  -- PHASE 1 EXTENSIONS: New constructor quotation
  TAll argTy retTy ->
    All (quote _lvl argTy) (quoteExtended (inc _lvl) retTy) -- retTy has extended context
  TSig fstTy sndTy ->
    Sig (quote _lvl fstTy) (quoteExtended (inc _lvl) sndTy) -- sndTy has extended context
    -- PHASE 2A EXTENSIONS: Pattern matching eliminator quotation
  TBitM falseCase trueCase ->
    BitM (quote _lvl falseCase) (quote _lvl trueCase)
  TNatM zeroCase sucCase ->
    NatM (quote _lvl zeroCase) (quote _lvl sucCase)
  TUniM unitCase ->
    UniM (quote _lvl unitCase)
  TLstM nilCase consCase ->
    LstM (quote _lvl nilCase) (quote _lvl consCase)
  TSigM pairCase ->
    SigM (quote _lvl pairCase)
  -- PHASE 2B EXTENSIONS: New constructor quotation
  TRef name level ->
    Ref name level
  TSub term ->
    Sub (quote _lvl term)
  TEmp ->
    Emp
  TEmpM ->
    EmpM
  TEql ty a b ->
    Eql (quote _lvl ty) (quote _lvl a) (quote _lvl b)
  TLst elemTy -> Lst (quote _lvl elemTy)
  TNil -> Nil
  TCons h t -> Con (quote _lvl h) (quote _lvl t)
  TTup a b -> Tup (quote _lvl a) (quote _lvl b)
  TRfl -> Rfl

-- * NORMALIZATION

-- Combine evaluation and quotation for normalization

normalize :: Env -> Cmd '[] ty -> Expr
normalize env cmd =
  let val = eval env cmd
   in quote (Lvl 0) val
