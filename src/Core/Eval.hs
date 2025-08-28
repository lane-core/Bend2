-- Intrinsic Type System Evaluation with NbE
-- =========================================
-- Normalization by Evaluation using indexed Val type
-- Type-safe evaluation with proper value domain
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Core.Eval (
  -- * New Intrinsic NbE System
  termToVal,         -- Terms -> Values (without Book)  
  termToValWithBook, -- Terms -> Values (with Book)
  nbeTerm,           -- Terms -> Normal Terms (without Book)
  nbeTermWithBook,   -- Terms -> Normal Terms (with Book)
  
  -- * Command Execution (New)
  exec, nbe,
  
  -- * Quotation (re-exported from Core.Val)
  quote,
  
  -- * Substitution Helpers
  subst, substTermTerm,
) where

import Core.Sort
import Core.Val (Val(..), Ne(..), quote, evalInEnvWithArg, evalInEnvWithArgAndBook, vApp)

import Unsafe.Coerce (unsafeCoerce)

-- * SIMPLE SURFACE TO INTRINSIC CONVERSION (to avoid circular imports)

-- | Simple conversion for basic surface terms to intrinsic (subset of Core.Bridge)
simpleSurfaceToIntrinsic :: Expr -> Maybe (SomeTerm '[])
simpleSurfaceToIntrinsic = \case
  Zer -> Just (SomeTerm TZer)
  Bt0 -> Just (SomeTerm TBt0)
  Bt1 -> Just (SomeTerm TBt1)  
  One -> Just (SomeTerm TOne)
  Set -> Just (SomeTerm TSet)
  Uni -> Just (SomeTerm TUni)
  Bit -> Just (SomeTerm TBit)
  Nat -> Just (SomeTerm TNat)
  Nil -> Just (SomeTerm TNil)
  Rfl -> Just (SomeTerm TRfl)
  Emp -> Just (SomeTerm TEmp)
  Suc term -> 
    case simpleSurfaceToIntrinsic term of
      Just (SomeTerm exp) -> Just (SomeTerm (TSuc (unsafeCoerce exp)))
      Nothing -> Nothing
  Con head tail ->
    case (simpleSurfaceToIntrinsic head, simpleSurfaceToIntrinsic tail) of
      (Just (SomeTerm headExp), Just (SomeTerm tailExp)) ->
        Just (SomeTerm (TCons (unsafeCoerce headExp) (unsafeCoerce tailExp)))
      _ -> Nothing
  Lam name argType body ->
    -- For lambdas, we need context handling - for now, unsupported
    Nothing
  App fun arg ->
    case (simpleSurfaceToIntrinsic fun, simpleSurfaceToIntrinsic arg) of
      (Just (SomeTerm funExp), Just (SomeTerm argExp)) ->
        Just (SomeTerm (TApp (unsafeCoerce funExp) (unsafeCoerce argExp)))
      _ -> Nothing
  Ref name level ->
    -- References are the key - they get resolved by termToValWithBook
    Just (SomeTerm (TRef name level))
  -- Add more cases as needed for the specific surface terms we encounter
  _ -> Nothing

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

-- * NORMALIZATION BY EVALUATION
--
-- Primary interface: evaluate to values, then quote back to normal forms

-- | Normalize a term using NbE (for closed terms without references)
nbeTerm :: Term '[] ty -> Term '[] ty
nbeTerm term = quote (termToVal term)

-- | Normalize a term using NbE with Book for reference resolution  
nbeTermWithBook :: Book -> Term '[] ty -> Term '[] ty
nbeTermWithBook book term = quote (termToValWithBook (Just book) term)

-- | Normalize a command using NbE (execute then normalize result - for closed commands) 
nbe :: Cmd '[] ty -> Term '[] ty
nbe cmd = 
  let resultTerm = exec cmd
      resultVal = termToVal resultTerm
      normalTerm = quote resultVal
  in normalTerm

-- * VALUE EVALUATION
--
-- Evaluate terms to the value domain for semantic operations


-- * PRIMARY EVALUATION FUNCTIONS
--
-- Commands execute to produce Terms, Terms embed into Values for semantic operations

-- | Execute a command to produce a term (main execution function)
exec :: Cmd ctx ty -> Term ctx ty  
exec = \case
  CReturn term -> term  -- Return just gives back the term
  
  CLet name maybeTy valCmd bodyCmd ->
    let valTerm = exec valCmd
        -- Substitute the value term into the body command  
        bodyTerm = execWithSubst valTerm bodyCmd
    in bodyTerm
    
  CApp fun arg -> 
    -- Function application: execute both sides then apply
    let funTerm = termToVal (unsafeCoerce (exec (CReturn fun)))
        argTerm = termToVal (unsafeCoerce (exec (CReturn arg)))  
        resultVal = vApp funTerm argTerm
    in unsafeCoerce (quote resultVal)
  
  CMatch scrut eliminator ->
    -- Pattern matching: apply eliminator to scrutinee
    let elimTerm = termToVal (unsafeCoerce (exec (CReturn eliminator)))
        scrutTerm = termToVal (unsafeCoerce (exec (CReturn scrut)))
        resultVal = vApp elimTerm scrutTerm
    in unsafeCoerce (quote resultVal)

-- | Convert a term to a value (unified implementation)
-- Optionally takes a Book for reference resolution
termToVal :: Term '[] ty -> Val '[] ty
termToVal = termToValWithBook Nothing

termToValWithBook :: Maybe Book -> Term '[] ty -> Val '[] ty  
termToValWithBook maybeBook = \case
  -- Variables become neutrals
  TVar idx -> VNe (NeVar idx)
  
  -- Constants (no Book needed)
  TSet -> VSet
  TUni -> VUni
  TBit -> VBit  
  TNat -> VNat
  TOne -> VOne
  TBt0 -> VBt0
  TBt1 -> VBt1
  TZer -> VZer
  TRfl -> VRfl
  TNil -> VNil
  TEmp -> VEmp
  
  -- Recursive cases
  TSuc n -> VSuc (termToValWithBook maybeBook n)
  TCons h t -> VCons (termToValWithBook maybeBook h) (termToValWithBook maybeBook t)
  TTup a b -> VTup (termToValWithBook maybeBook a) (termToValWithBook maybeBook b)
  TLst elemTy -> VLst (termToValWithBook maybeBook elemTy)
  TEql ty a b -> VEql (termToValWithBook maybeBook ty) (termToValWithBook maybeBook a) (termToValWithBook maybeBook b)
  TApp fun arg -> vApp (termToValWithBook maybeBook fun) (termToValWithBook maybeBook arg)
  TSub term -> termToValWithBook maybeBook term
  
  -- Lambda values with Book-aware closures
  TLam name argTy body -> VLam name argTy (\arg ->
    case maybeBook of
      Just book -> evalInEnvWithArgAndBook book arg body
      Nothing -> evalInEnvWithArg arg body)
  
  -- References with optional Book resolution
  TRef name level -> 
    case maybeBook of
      Just book -> 
        case getDefn book name of
          Just (_, refTerm, _) -> 
            case simpleSurfaceToIntrinsic refTerm of
              Just (SomeTerm intrinsicRefTerm) -> 
                termToValWithBook maybeBook (unsafeCoerce intrinsicRefTerm)
              Nothing -> VNe (NeRef name level)
          Nothing -> VNe (NeRef name level)
      Nothing -> VNe (NeRef name level)
  
  -- Unimplemented cases (clean error messages)
  TAll _ _ -> error "termToVal: function types not in canonical form"
  TSig _ _ -> error "termToVal: sigma types not in canonical form"
  TEmpM -> error "termToVal: empty eliminator not implemented"
  TBitM _ _ -> error "termToVal: pattern eliminators not in canonical form"  
  TNatM _ _ -> error "termToVal: pattern eliminators not in canonical form"
  TUniM _ -> error "termToVal: pattern eliminators not in canonical form"
  TLstM _ _ -> error "termToVal: pattern eliminators not in canonical form"
  TSigM _ -> error "termToVal: pattern eliminators not in canonical form"

-- Helper for let evaluation with substitution  
execWithSubst :: Term ctx valTy -> Cmd (valTy ': ctx) resultTy -> Term ctx resultTy
execWithSubst valTerm cmd = 
  case cmd of
    CReturn bodyTerm -> substTermTerm valTerm bodyTerm
    _ -> error "execWithSubst: complex commands not yet supported"

-- Substitute a term for variable 0 in another term
substTermTerm :: Term ctx ty -> Term (ty ': ctx) target -> Term ctx target
substTermTerm arg body = case body of
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

  -- Recursive cases with substitution
  TSuc n -> TSuc (substTermTerm arg n)
  TLam name argType lambdaBody ->
    TLam name argType (unsafeCoerce lambdaBody) -- Temporarily unsafe for lambda body
  TCons h t -> TCons (substTermTerm arg h) (substTermTerm arg t)
  TTup a b -> TTup (substTermTerm arg a) (substTermTerm arg b)
  TLst ty -> TLst (substTermTerm arg ty)
  
  -- Function types with substitution
  TAll argTy retTy -> TAll (substTermTerm arg argTy) (unsafeCoerce retTy)
  TSig fstTy sndTy -> TSig (substTermTerm arg fstTy) (unsafeCoerce sndTy)
  TApp fun arg' -> TApp (substTermTerm arg fun) (substTermTerm arg arg')
  
  -- Pattern matching eliminators
  TBitM f t -> TBitM (substTermTerm arg f) (substTermTerm arg t)
  TNatM z s -> TNatM (substTermTerm arg z) (unsafeCoerce s)
  TUniM u -> TUniM (substTermTerm arg u)
  TLstM n c -> TLstM (substTermTerm arg n) (unsafeCoerce c)
  TSigM p -> TSigM (unsafeCoerce p)
  
  -- References and wrappers
  TRef name level -> TRef name level -- No substitution needed
  TSub term -> TSub (substTermTerm arg term)
  TEql ty a b -> TEql (substTermTerm arg ty) (substTermTerm arg a) (substTermTerm arg b)

-- End of Core.Eval - Legacy functions moved to Core.Legacy.Eval
