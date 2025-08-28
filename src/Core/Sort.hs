-- Intrinsic Type System Foundation (Fixed)
-- =======================================
-- Essential types and constructors for intrinsic typing
-- Clean, working implementation with proper type constraints
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Sort where

-- import Core.Sort

import Data.Int (Int32, Int64)
import Data.Kind
import Data.List (intercalate)
import Data.Map qualified as M
import Data.Maybe (fromJust, fromMaybe)
import Data.Set qualified as S
import Data.Word (Word32, Word64)

-- Bend's Surface Expression Type (untyped, what users write)
data Expr
  = -- Variables
    Var Name Int -- x
  | Ref Name Int -- x, Reduce?
  | Sub Expr -- x
  | -- Definitions
    Fix Name Body -- μx. f
  | Let Name (Maybe Expr) Expr Body -- !x : T = v; f
  | Use Name Expr Body -- !x = v; f
  | -- Universe
    Set -- Set
  | -- Annotation
    Chk Expr Expr -- x::t
  | Tst Expr -- trust x
  | -- Empty
    Emp -- Empty
  | EmpM -- λ{}
  | -- Unit
    Uni -- Unit
  | One -- ()
  | UniM Expr -- λ{():f}
  | -- Bool
    Bit -- Bool
  | Bt0 -- False
  | Bt1 -- True
  | BitM Expr Expr -- λ{False:t;True:t}
  | -- Nat
    Nat -- Nat
  | Zer -- 0
  | Suc Expr -- ↑n
  | NatM Expr Expr -- λ{0n:z;1n+:s}
  | -- List
    Lst Expr -- T[]
  | Nil -- []
  | Con Expr Expr -- h<>t
  | LstM Expr Expr -- λ{[]:n;<>:c}
  | -- Enum
    Enu [String] -- {&foo,&bar...}
  | Sym String -- &foo
  | EnuM [(String, Expr)] Expr -- λ{&foo:f;&bar:b;...d}
  | -- Numbers
    Num NTyp -- CHR | U64 | I64 | F64
  | Val NVal -- 123 | +123 | +123.0
  | Op2 NOp2 Expr Expr -- x + y
  | Op1 NOp1 Expr -- !x
  | -- Pair
    Sig Expr Expr -- ΣA.B
  | Tup Expr Expr -- (a,b)
  | SigM Expr -- λ{(,):f}
  | -- Function
    All Expr Expr -- ∀A.B
  | Lam Name (Maybe Expr) Body -- λx.f | λx:A.f
  | App Expr Expr -- (f x)
  | -- Equality
    Eql Expr Expr Expr -- T{a==b}
  | Rfl -- {==}
  | EqlM Expr -- λ{{==}:f}
  | Rwt Expr Expr -- rewrite e f
  | -- MetaVar
    Met Name Expr [Expr] -- ?N:T{x0,x1,...}
  | -- Supperpositions
    Era
  | Sup Expr Expr Expr -- &L{a,b}
  | SupM Expr Expr -- λ{&L{,}:f}
  | -- Errors
    Loc Span Expr -- x
  | -- Logging
    Log Expr Expr -- log s ; x
  | -- Primitive
    Pri PriF -- SOME_FUNC
  | -- Sugars
    Pat [Expr] [Move] [Case] -- match x ... { with k=v ... ; case @A ...: F ; ... }
  | Frk Expr Expr Expr -- fork L:a else:b

-- * TYPE FAMILIES FOR CONTEXT MANIPULATION

-- Safe substitution and context operations

-- | Weaken a term from empty context to any context
type family Weaken (ctx :: [Expr]) (ty :: Expr) :: Expr where
  Weaken ctx ty = ty -- Type doesn't change, only context

-- | Shift context by removing first element
type family Shift (ctx :: [Expr]) :: [Expr] where
  Shift '[] = '[]
  Shift (x ': xs) = xs

-- | Extend context with a type (for dependent types)
type family Extend (ty :: Expr) (ctx :: [Expr]) :: [Expr] where
  Extend ty ctx = ty ': ctx

-- * DE BRUIJN INDICES

-- Type-safe de Bruijn indices with context tracking

data Idx :: [Expr] -> Expr -> Type where
  Here :: Idx (ty ': ctx) ty
  There :: Idx ctx ty -> Idx (ty' ': ctx) ty

-- * VALUES (Positive Types - Sequent Calculus)

-- Pure values: data constructors, variables, canonical forms

data Term :: [Expr] -> Expr -> Type where
  -- Variables
  TVar :: Idx ctx ty -> Term ctx ty
  -- Universe hierarchy
  TSet :: Term ctx 'Set
  TUni :: Term ctx 'Set -- Unit : Set
  TBit :: Term ctx 'Set -- Bool : Set
  TNat :: Term ctx 'Set -- Nat : Set

  -- Unit type values
  TOne :: Term ctx 'Uni -- () : Unit

  -- Boolean values
  TBt0 :: Term ctx 'Bit -- False : Bool
  TBt1 :: Term ctx 'Bit -- True : Bool

  -- Natural number values
  TZer :: Term ctx 'Nat -- 0 : Nat
  TSuc :: Term ctx 'Nat -> Term ctx 'Nat -- S(n) : Nat

  -- Function values (simplified - no closures for now)
  TLam ::
    String ->
    Expr ->
    (Term (arg ': ctx) ret) ->
    Term ctx ('All arg ret)
  -- PHASE 1 EXTENSIONS: Core Programming Features

  -- Function Types (Dependent Products) - ∀A.B
  TAll :: Term ctx 'Set -> Term (arg ': ctx) 'Set -> Term ctx 'Set
  -- Product Types (Dependent Sums) - ΣA.B
  TSig :: Term ctx 'Set -> Term (fst ': ctx) 'Set -> Term ctx 'Set
  -- Function Application (pure operation)
  TApp :: Term ctx ('All arg ret) -> Term ctx arg -> Term ctx ret
  -- List values
  TLst :: Term ctx 'Set -> Term ctx 'Set -- [T] : Set
  TNil :: Term ctx ('Lst a) -- [] : [a]
  TCons :: Term ctx a -> Term ctx ('Lst a) -> Term ctx ('Lst a) -- h::t

  -- Pair values
  TTup :: Term ctx a -> Term ctx b -> Term ctx ('Sig a b) -- (a,b) : Σa:A.B

  -- Equality values
  TRfl :: Term ctx ('Eql t a a) -- refl : a = a

  -- PHASE 2A EXTENSIONS: Pattern Matching Eliminators

  -- Boolean eliminator: λ{False:f;True:t}
  TBitM :: Term ctx ret -> Term ctx ret -> Term ctx ('All 'Bit ret)
  -- Natural number eliminator: λ{0:z;S(p):s}
  TNatM :: Term ctx ret -> Term ctx ('All 'Nat ret) -> Term ctx ('All 'Nat ret)
  -- Unit eliminator: λ{():f}
  TUniM :: Term ctx ret -> Term ctx ('All 'Uni ret)
  -- List eliminator: λ{[]:n;h::t:c}
  TLstM ::
    Term ctx ret ->
    Term ctx ('All a ('All ('Lst a) ret)) ->
    Term ctx ('All ('Lst a) ret)
  -- Pair eliminator: λ{(a,b):f}
  TSigM ::
    Term ctx ('All a ('All b ret)) ->
    Term ctx ('All ('Sig a b) ret)
  -- PHASE 2B EXTENSIONS: References and Simple Terms

  -- Book references
  TRef :: String -> Int -> Term ctx ty -- Reference to definition in book

  -- Term wrapping/annotation
  TSub :: Term ctx ty -> Term ctx ty -- Substitution wrapper

  -- Empty types (simpler than functions)
  TEmp :: Term ctx 'Emp -- Empty type (⊥)
  TEmpM :: Term ctx ('All 'Emp ret) -- Empty eliminator λ{}

  -- Equality types (without dependency for now)
  TEql :: Term ctx 'Set -> Term ctx ty -> Term ctx ty -> Term ctx 'Set

-- * COMMANDS (Negative Types - Sequent Calculus)

-- Effectful commands: pattern matching, application, control flow

data Cmd :: [Expr] -> Expr -> Type where
  -- Return a value (lift from values to commands)
  CReturn :: Term ctx ty -> Cmd ctx ty
  -- PHASE 1 EXTENSIONS: Enhanced Let bindings

  -- Let binding with optional type annotation
  CLet ::
    String ->
    Maybe (Term ctx 'Set) ->
    Cmd ctx valType ->
    Cmd (valType ': ctx) resultType ->
    Cmd ctx resultType
  -- PHASE 2A EXTENSIONS: Pattern Matching Command

  -- Function application (the key command) - kept for compatibility
  CApp :: Term ctx (All arg ret) -> Term ctx arg -> Cmd ctx ret
  -- Pattern match command: match scrut with { pat -> body }
  CMatch ::
    Term ctx scrutTy ->
    Term ctx ('All scrutTy retTy) -> -- eliminator function
    Cmd ctx retTy

-- * PATTERNS (Simplified)

-- Essential pattern matching without complex type arithmetic

data Pattern :: Expr -> Type where
  PVar :: String -> Pattern ty -- Variable pattern
  PZer :: Pattern 'Nat -- Zero pattern
  PSuc :: Pattern 'Nat -- Successor
  PBt0 :: Pattern 'Bit -- False pattern
  PBt1 :: Pattern 'Bit -- True pattern
  POne :: Pattern 'Uni -- Unit pattern
  PNil :: Pattern ('Lst a) -- Empty list
  PCons ::
    Pattern a ->
    Pattern ('Lst a) ->
    Pattern ('Lst a) -- List cons

-- * UTILITY TYPES

-- Helper types for type-safe operations

-- | Level for quotation
newtype Lvl = Lvl Int deriving (Show, Eq)

-- | Depth for equality checking
newtype Depth = Depth Int deriving (Show, Eq)

-- | Existentially quantified term (for surface conversion)
data SomeTerm ctx = forall ty. SomeTerm (Term ctx ty)

-- | Existentially quantified index (for variable lookup)
data SomeIdx ctx = forall ty. SomeIdx (Idx ctx ty)

-- * CONVERSION CONTEXT

-- Environment for context-aware surface to intrinsic conversion

-- | Variable environment mapping names to De Bruijn indices
type VarEnv ctx = [(String, SomeIdx ctx)]

-- | Conversion context with variable and type environments
data TStore ctx = TStore
  { varEnv :: VarEnv ctx
  , typeEnv :: [(String, Expr)] -- for type lookup
  }

-- * UTILITY FUNCTIONS

-- Essential operations on indices and contexts

-- | Convert de Bruijn index to integer (for debugging)
idxToInt :: Idx ctx ty -> Int
idxToInt Here = 0
idxToInt (There idx) = 1 + idxToInt idx

-- | Increment level
inc :: Lvl -> Lvl
inc (Lvl n) = Lvl (n + 1)

-- | Decrement depth
decDepth :: Depth -> Depth
decDepth (Depth n) = Depth (max 0 (n - 1))

-- | Maximum recursion depth for equality
maxDepth :: Depth
maxDepth = Depth 1000

-- * SIMPLE ENVIRONMENT (No GADT complexity)

-- Legacy environment types moved to Core.Legacy.Eval

-- * CONVERSION UTILITIES

-- Functions for managing conversion context and variable environments

-- | Empty conversion context
emptyTStore :: TStore '[]
emptyTStore = TStore{varEnv = [], typeEnv = []}

-- | Extend variable environment with new binding
extendVarEnv :: String -> VarEnv ctx -> VarEnv (ty ': ctx)
extendVarEnv name env = (name, SomeIdx Here) : shiftVarEnv env

-- | Shift all indices in variable environment (for context extension)
shiftVarEnv :: VarEnv ctx -> VarEnv (ty ': ctx)
shiftVarEnv = map (\(name, SomeIdx idx) -> (name, SomeIdx (There idx)))

-- * CONTEXT OPERATIONS

-- Type-safe context manipulation functions

{- | Weaken a term from empty context to any context
This is safe because terms with no free variables can be used in any context
NOTE: Limited to simple types without dependent contexts for now
-}
weakenTerm :: Term '[] ty -> Term ctx ty
weakenTerm = \case
  -- Variables - impossible in empty context (but compiler doesn't know this)
  TVar idx -> case idx of {}
  -- Empty case - no variables possible in empty context

  -- Constants can be moved to any context
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
  -- Recursive cases (simple types only)
  TSuc n -> TSuc (weakenTerm n)
  TCons h t -> TCons (weakenTerm h) (weakenTerm t)
  TTup a b -> TTup (weakenTerm a) (weakenTerm b)
  TLst ty -> TLst (weakenTerm ty)
  -- Simple function application
  TApp fun arg -> TApp (weakenTerm fun) (weakenTerm arg)
  -- Pattern eliminators (simple cases)
  TBitM f t -> TBitM (weakenTerm f) (weakenTerm t)
  TUniM u -> TUniM (weakenTerm u)
  -- References and simple terms
  TRef name level -> TRef name level
  TSub term -> TSub (weakenTerm term)
  TEql ty a b -> TEql (weakenTerm ty) (weakenTerm a) (weakenTerm b)
  -- Complex dependent types: not supported in weakenTerm for now
  -- These require more sophisticated context manipulation
  TAll{} -> error "weakenTerm: TAll not supported - requires context extension"
  TSig{} -> error "weakenTerm: TSig not supported - requires context extension"
  TLam{} -> error "weakenTerm: TLam not supported - requires context extension"
  TNatM{} -> error "weakenTerm: TNatM not supported - requires function context"
  TLstM{} -> error "weakenTerm: TLstM not supported - requires function context"
  TSigM{} -> error "weakenTerm: TSigM not supported - requires function context"

-- Legacy definitions from old Type.hs
type Body = Expr -> Expr
type Name = String
type Case = ([Expr], Expr)
type Move = (String, Expr)

-- Error Location
data Span = Span
  { spanBeg :: (Int, Int)
  , spanEnd :: (Int, Int)
  , spanPth :: FilePath -- original file path
  , spanSrc :: String -- source content
  }
  deriving (Eq, Ord)

data NTyp
  = U64_T
  | I64_T
  | F64_T
  | CHR_T
  deriving (Show, Eq)

data NVal
  = U64_V Word64
  | I64_V Int64
  | F64_V Double
  | CHR_V Char
  deriving (Show, Eq)

data NOp2
  = ADD
  | SUB
  | MUL
  | DIV
  | MOD
  | POW
  | EQL
  | NEQ
  | LST
  | GRT
  | LEQ
  | GEQ
  | AND
  | OR
  | XOR
  | SHL
  | SHR
  deriving (Show, Eq)

data NOp1
  = NOT
  | NEG
  deriving (Show, Eq)

data PriF
  = U64_TO_CHAR
  | CHAR_TO_U64
  | HVM_INC
  | HVM_DEC
  deriving (Show, Eq)

data Bits = O Bits | I Bits | E deriving (Show)

{- | MIGRATION COMPATIBILITY: Alias for the old surface type name
TODO: Remove this once all modules are migrated to use 'Expr'
-}

-- Book of Definitions
type Inj = Bool -- "is injective" flag. improves pretty printing

type Defn = (Inj, Expr, Expr)
data Book = Book (M.Map Name Defn) [Name]

-- Substitution Map
type Subs = [(Expr, Expr)]

type Ctx = [Expr]

-- Legacy ctx
newtype SCtx = SCtx [(Name, Expr, Expr)]

emptySCtx :: SCtx
emptySCtx = SCtx []

extendSCtx :: String -> Expr -> Expr -> SCtx -> SCtx
extendSCtx name typ val (SCtx env) = SCtx ((name, typ, val) : env)

-- Errors
data Error
  = CantInfer Span SCtx (Maybe String)
  | Unsupported Span SCtx (Maybe String)
  | Undefined Span SCtx Name (Maybe String)
  | TypeMismatch Span SCtx Expr Expr (Maybe String)
  | ExprMismatch Span SCtx Expr Expr (Maybe String)
  | IncompleteMatch Span SCtx (Maybe String)
  | UnknownTermination Expr
  | ImportError Span String

data Result a
  = Done a
  | Fail Error

instance Functor Result where
  fmap f (Done a) = Done (f a)
  fmap _ (Fail e) = Fail e

instance Applicative Result where
  pure = Done
  Done f <*> Done a = Done (f a)
  Fail e <*> _ = Fail e
  _ <*> Fail e = Fail e

instance Monad Result where
  Done a >>= f = f a
  Fail e >>= _ = Fail e

-- Peano naturals at both type‑ and value‑level
data Nat = Z | S Nat

data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- Type‑level addition
type family Add (n :: Nat) (m :: Nat) :: Nat where
  Add Z m = m
  Add (S n) m = S (Add n m)

-- Adds two type-level SNats
addSNat :: SNat n -> SNat m -> SNat (Add n m)
addSNat SZ m = m
addSNat (SS n) m = SS (addSNat n m)

-- -- Arg<n> = n‑ary function returning Expr
type family Arg (n :: Nat) :: Type where
  Arg Z = Expr
  Arg (S p) = Expr -> Arg p

-- LHS = pair of arity and a constructor taking exactly that many args
data LHS where
  LHS :: SNat k -> (Expr -> Arg k) -> LHS

--
-- Utils
-- -----

getDefn :: Book -> Name -> Maybe Defn
getDefn (Book defs _) name = M.lookup name defs

cut :: Expr -> Expr
cut (Loc _ t) = cut t
cut (Chk x _) = cut x
cut t = t

unlam :: Name -> Int -> (Expr -> Expr) -> Expr
unlam k d f = f (Var k d)

collectArgs :: Expr -> ([(String, Expr)], Expr)
collectArgs = go []
 where
  go acc (Loc _ t) = go acc t
  go acc (All t (Lam k ty f)) = go (acc ++ [(k, t)]) (f (Var k 0))
  go acc goal = (acc, goal)

collectApps :: Expr -> [Expr] -> (Expr, [Expr])
collectApps (cut -> App f x) args = collectApps f (x : args)
collectApps f args = (f, args)

noSpan :: Span
noSpan = Span (0, 0) (0, 0) "" ""

flattenTup :: Expr -> [Expr]
flattenTup (Tup l r) = l : flattenTup r
flattenTup t = [t]

isLam :: Expr -> Bool
isLam (Loc _ f) = isLam f
isLam Lam{} = True
isLam EmpM = True
isLam UniM{} = True
isLam BitM{} = True
isLam NatM{} = True
isLam LstM{} = True
isLam EnuM{} = True
isLam SigM{} = True
isLam SupM{} = True
isLam EqlM{} = True
isLam _ = False

-- | Collects all variable usages with their names and depths
collectVars :: Expr -> [(String, Int)]
collectVars t = case t of
  Var k i -> [(k, i)]
  Ref k i -> [] -- Refs don't shadow
  Sub t -> collectVars t
  Fix k f -> collectVars (f (Var k 0))
  Let k t v f -> maybe [] collectVars t ++ collectVars v ++ collectVars (f (Var k 0))
  Use k v f -> collectVars v ++ collectVars (f (Var k 0))
  Chk x t -> collectVars x ++ collectVars t
  Tst x -> collectVars x
  UniM f -> collectVars f
  BitM f t -> collectVars f ++ collectVars t
  NatM z s -> collectVars z ++ collectVars s
  Lst t -> collectVars t
  Con h t -> collectVars h ++ collectVars t
  LstM n c -> collectVars n ++ collectVars c
  EnuM cs d -> concatMap (collectVars . snd) cs ++ collectVars d
  Op2 _ a b -> collectVars a ++ collectVars b
  Op1 _ a -> collectVars a
  Sig t f -> collectVars t ++ collectVars f
  Tup a b -> collectVars a ++ collectVars b
  SigM f -> collectVars f
  All t f -> collectVars t ++ collectVars f
  Lam k t f -> maybe [] collectVars t ++ collectVars (f (Var k 0))
  App f a -> collectVars f ++ collectVars a
  Eql t a b -> collectVars t ++ collectVars a ++ collectVars b
  EqlM f -> collectVars f
  Rwt e f -> collectVars e ++ collectVars f
  Met n t ctx -> collectVars t ++ concatMap collectVars ctx
  Sup l a b -> collectVars l ++ collectVars a ++ collectVars b
  SupM l f -> collectVars l ++ collectVars f
  Loc _ t -> collectVars t
  Log s x -> collectVars s ++ collectVars x
  Pat ts ms cs ->
    concatMap collectVars ts
      ++ concatMap (collectVars . snd) ms
      ++ concatMap (\(ps, t) -> concatMap collectVars ps ++ collectVars t) cs
  Frk l a b -> collectVars l ++ collectVars a ++ collectVars b
  _ -> []
