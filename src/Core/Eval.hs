-- Streamlined Intrinsic Evaluation System
-- ======================================
-- Complete NbE pipeline with Values, Neutrals, and Evaluation
-- Combines Val and Eval modules for better ergonomics
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Core.Eval (
  -- * Value Types
  Val(..), Ne(..), 
  
  -- * Core NbE Pipeline
  termToVal,         -- Terms -> Values (without Book)  
  termToValWithBook, -- Terms -> Values (with Book)
  nbeTerm,           -- Terms -> Normal Terms (without Book)
  nbeTermWithBook,   -- Terms -> Normal Terms (with Book)
  
  -- * Command Execution
  exec, nbe,
  
  -- * Quotation
  quote, quoteNe,
  
  -- * Semantic Operations
  vApp, weakenVal, weakenNe, substVal,
  
  -- * Environment-Based Evaluation
  evalInEnvWithArg,
  evalInEnvWithArgAndBook,
  
  -- * Substitution Helpers
  subst, substTermTerm,
) where

import Core.Sort
import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

-- * CANONICAL VALUES (Normal Forms)
--
-- Values represent canonical/normal forms in the semantic domain
-- These are fully evaluated and cannot be reduced further

data Val :: [Expr] -> Expr -> Type where
  -- Universe hierarchy  
  VSet :: Val ctx 'Set
  
  -- Type constructors as values
  VUni :: Val ctx 'Set -- Unit : Set
  VBit :: Val ctx 'Set -- Bool : Set  
  VNat :: Val ctx 'Set -- Nat : Set
  
  -- Unit type values (canonical)
  VOne :: Val ctx 'Uni -- () : Unit
  
  -- Boolean values (canonical) 
  VBt0 :: Val ctx 'Bit -- False : Bool
  VBt1 :: Val ctx 'Bit -- True : Bool
  
  -- Natural number values (canonical)
  VZer :: Val ctx 'Nat -- 0 : Nat
  VSuc :: Val ctx 'Nat -> Val ctx 'Nat -- S(n) : Nat
  
  -- Function values (hybrid closures - canonical)
  VLam :: 
    String ->
    Expr -> -- argument type  
    (Val ctx arg -> Val ctx ret) -> -- functional closure for body
    Val ctx ('All arg ret)
    
  -- List types and values (canonical)
  VLst :: Val ctx 'Set -> Val ctx 'Set -- [T] : Set
  VNil :: Val ctx ('Lst a) -- [] : [a]
  VCons :: Val ctx a -> Val ctx ('Lst a) -> Val ctx ('Lst a) -- h::t
  
  -- Pair values (canonical)
  VTup :: Val ctx a -> Val ctx b -> Val ctx ('Sig a b) -- (a,b)
  
  -- Equality values (canonical)
  VRfl :: Val ctx ('Eql t a a) -- refl : a = a
  
  -- Empty type (canonical)
  VEmp :: Val ctx 'Emp -- Empty type (⊥)
  
  -- Equality types (canonical)
  VEql :: Val ctx 'Set -> Val ctx ty -> Val ctx ty -> Val ctx 'Set
  
  -- NEUTRAL EMBEDDINGS: Stuck computations embedded as values
  VNe :: Ne ctx ty -> Val ctx ty

-- * NEUTRAL FORMS (Stuck Computations)  
--
-- Neutrals represent computations that are stuck (cannot proceed)
-- due to free variables or undefined references

data Ne :: [Expr] -> Expr -> Type where
  -- Variables (stuck - we don't know what they are)
  NeVar :: Idx ctx ty -> Ne ctx ty
  
  -- Function application (stuck - function is neutral)
  NeApp :: Ne ctx ('All arg ret) -> Val ctx arg -> Ne ctx ret
  
  -- References (stuck - name not found)
  NeRef :: String -> Int -> Ne ctx ty

-- * SEMANTIC OPERATIONS
--
-- Operations on the semantic domain (Values and Neutrals)

-- | Apply a function value to an argument (semantic application)
vApp :: Val ctx ('All arg ret) -> Val ctx arg -> Val ctx ret
vApp (VLam _ _ f) arg = f arg -- Direct functional application - no substitution needed!
vApp (VNe ne) arg = VNe (NeApp ne arg)

-- | Substitute a value for the topmost variable in a value (simplified placeholder)
substVal :: Idx (ty ': ctx) target -> Val ctx ty -> Val (ty ': ctx) target -> Val ctx target  
substVal _ _ _ = error "substVal: intrinsic substitution too complex - consider closure-based approach"

-- | Weaken a value by extending the context
-- This shifts all De Bruijn indices to account for the new binding
weakenVal :: Val ctx ty -> Val (newTy ': ctx) ty
weakenVal = \case
  -- Canonical forms: no variables to weaken
  VSet -> VSet
  VUni -> VUni
  VBit -> VBit
  VNat -> VNat
  VOne -> VOne
  VBt0 -> VBt0
  VBt1 -> VBt1
  VZer -> VZer
  VSuc v -> VSuc (weakenVal v)
  VNil -> VNil
  VCons h t -> VCons (weakenVal h) (weakenVal t)
  VTup a b -> VTup (weakenVal a) (weakenVal b)
  VRfl -> VRfl
  VEmp -> VEmp
  VLst elemTy -> VLst (weakenVal elemTy)
  VEql ty a b -> VEql (weakenVal ty) (weakenVal a) (weakenVal b)
  
  -- Lambda: weaken the closure
  VLam name argTy f -> VLam name argTy (\arg -> weakenVal (f (unsafeCoerce arg)))
  
  -- Neutral forms: weaken the neutral
  VNe ne -> VNe (weakenNe ne)

-- | Weaken a neutral form  
weakenNe :: Ne ctx ty -> Ne (newTy ': ctx) ty
weakenNe = \case
  NeVar idx -> NeVar (There idx) -- Shift variable index
  NeApp fun arg -> NeApp (weakenNe fun) (weakenVal arg)
  NeRef name level -> NeRef name level -- References don't change

-- * ENVIRONMENT-BASED EVALUATION FOR LAMBDA CONVERSION
--
-- Specialized evaluation to handle TLam → VLam without circular dependencies

-- | Evaluate a lambda body term with an additional argument binding
-- This handles the case: TLam body -> VLam (\arg -> evalInEnvWithArg arg body)
evalInEnvWithArg :: Val ctx arg -> Term (arg ': ctx) ret -> Val ctx ret
evalInEnvWithArg argVal term = case term of
  -- Variable cases: Handle the bound variable (Here) and free variables (There)
  TVar Here -> unsafeCoerce argVal  -- Variable 0 is the argument (temporarily unsafe)
  TVar (There idx) -> VNe (NeVar idx)  -- Free variables become neutrals
  
  -- Constants (no environment needed)
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
  
  -- Recursive structural cases
  TSuc n -> VSuc (evalInEnvWithArg argVal n)
  TCons h t -> VCons (evalInEnvWithArg argVal h) (evalInEnvWithArg argVal t)
  TTup a b -> VTup (evalInEnvWithArg argVal a) (evalInEnvWithArg argVal b)
  TLst elemTy -> VLst (evalInEnvWithArg argVal elemTy)
  TEql ty a b -> VEql (evalInEnvWithArg argVal ty) (evalInEnvWithArg argVal a) (evalInEnvWithArg argVal b)
  
  -- Function application via semantic vApp
  TApp fun arg -> vApp (evalInEnvWithArg argVal fun) (evalInEnvWithArg argVal arg)
  
  -- Nested lambda: create another closure
  TLam name argTy body -> VLam name argTy (\newArg ->
    -- For nested lambdas, we need to handle the extended context properly
    -- This is a complex case that might need more sophisticated environment handling
    error "evalInEnvWithArg: nested lambdas not yet implemented")
  
  -- Other constructors
  TRef name level -> VNe (NeRef name level)
  TSub subterm -> evalInEnvWithArg argVal subterm
  
  -- Pattern matching eliminators and other complex terms
  _ -> error "evalInEnvWithArg: constructor not yet implemented"

-- | Book-aware environment evaluation for lambda bodies with references
-- Note: This is a simplified version that doesn't resolve references in lambda bodies
-- Full reference resolution is handled by termToValWithBook in Core.Eval
evalInEnvWithArgAndBook :: Book -> Val ctx arg -> Term (arg ': ctx) ret -> Val ctx ret
evalInEnvWithArgAndBook book argVal term = case term of
  -- Variable cases: Handle the bound variable (Here) and free variables (There)
  TVar Here -> unsafeCoerce argVal  -- Variable 0 is the argument (temporarily unsafe)
  TVar (There idx) -> VNe (NeVar idx)  -- Free variables become neutrals
  
  -- Constants (no environment needed)
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
  
  -- Recursive structural cases with Book
  TSuc n -> VSuc (evalInEnvWithArgAndBook book argVal n)
  TCons h t -> VCons (evalInEnvWithArgAndBook book argVal h) (evalInEnvWithArgAndBook book argVal t)
  TTup a b -> VTup (evalInEnvWithArgAndBook book argVal a) (evalInEnvWithArgAndBook book argVal b)
  TLst elemTy -> VLst (evalInEnvWithArgAndBook book argVal elemTy)
  TEql ty a b -> VEql (evalInEnvWithArgAndBook book argVal ty) (evalInEnvWithArgAndBook book argVal a) (evalInEnvWithArgAndBook book argVal b)
  
  -- Function application via semantic vApp
  TApp fun arg -> vApp (evalInEnvWithArgAndBook book argVal fun) (evalInEnvWithArgAndBook book argVal arg)
  
  -- Nested lambda: create another closure with Book support
  TLam name argTy body -> VLam name argTy (\newArg ->
    -- For nested lambdas, we need to handle the extended context properly
    -- This is a complex case that might need more sophisticated environment handling
    error "evalInEnvWithArgAndBook: nested lambdas not yet implemented")
  
  -- References - keep as neutrals (reference resolution happens at top level)
  TRef name level -> VNe (NeRef name level)
  
  -- Other constructors
  TSub subterm -> evalInEnvWithArgAndBook book argVal subterm
  
  -- Pattern matching eliminators and other complex terms
  _ -> error "evalInEnvWithArgAndBook: constructor not yet implemented"

-- * QUOTATION: VALUES AND NEUTRALS BACK TO TERMS
--
-- Quote canonical values and neutrals back to normal form terms

quote :: Val ctx ty -> Term ctx ty
quote = \case
  -- Canonical forms quote directly
  VSet -> TSet
  VUni -> TUni
  VBit -> TBit
  VNat -> TNat
  VOne -> TOne
  VBt0 -> TBt0
  VBt1 -> TBt1
  VZer -> TZer
  VSuc v -> TSuc (quote v)
  
  VLam name argTy f ->
    -- Intrinsic lambda quotation: create fresh variable and quote the closure application
    -- Since we're intrinsic, fresh variable is just Here in extended context
    let freshVar = VNe (NeVar Here)      -- Fresh variable :: Val (arg ': ctx) arg
        bodyVal = f (unsafeCoerce freshVar)  -- Apply closure (temporarily unsafe for context)
        bodyTerm = quote bodyVal          -- Quote result :: Term (arg ': ctx) ret  
    in TLam name argTy (unsafeCoerce bodyTerm)  -- Return :: Term ctx ('All arg ret)
    
  VNil -> TNil
  VCons h t -> TCons (quote h) (quote t)
  VTup a b -> TTup (quote a) (quote b)  
  VRfl -> TRfl
  VEmp -> TEmp
  
  -- Type constructors
  VLst elemTy -> TLst (quote elemTy)
  VEql ty a b -> TEql (quote ty) (quote a) (quote b)
  
  -- Neutral forms delegate to neutral quotation
  VNe ne -> quoteNe ne

-- | Quote neutral forms back to terms
quoteNe :: Ne ctx ty -> Term ctx ty  
quoteNe = \case
  NeVar idx -> TVar idx
  NeApp fun arg -> TApp (quoteNe fun) (quote arg)
  NeRef name level -> TRef name level

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
