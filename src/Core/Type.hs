{-# LANGUAGE ViewPatterns #-}

module Core.Type where

import Data.List (intercalate)
import Debug.Trace
import Highlight (highlightError)
import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S

data Bits = O Bits | I Bits | E deriving Show
type Name = String
type Body = Term -> Term
type Case = ([Term], Term)
type Move = (String, Term)
type Type = Term

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
  = ADD | SUB | MUL | DIV | MOD | POW
  | EQL | NEQ  
  | LST | GRT | LEQ | GEQ
  | AND | OR  | XOR
  | SHL | SHR
  deriving (Show, Eq)

data NOp1
  = NOT | NEG
  deriving (Show, Eq)

data PriF
  = U64_TO_CHAR
  | CHAR_TO_U64
  deriving (Show, Eq)

-- -- Bend's Term Type
-- data Term
  -- -- Variables
  -- = Var Name Int -- x
  -- | Ref Name     -- x
  -- | Sub Term     -- x

  -- -- Definitions
  -- | Fix Name Body                   -- μx. f
  -- | Let Name (Maybe Term) Term Body -- !x : T = v; f

  -- -- Universe
  -- | Set -- Set

  -- -- Annotation
  -- | Chk Term Type -- x::t

  -- -- Empty
  -- | Emp       -- Empty
  -- | EmpM Term -- ~x{}

  -- -- Unit
  -- | Uni            -- Unit
  -- | One            -- ()
  -- | UniM Term Term -- ~x{():f}

  -- -- Bool
  -- | Bit                 -- Bool
  -- | Bt0                 -- False
  -- | Bt1                 -- True
  -- | BitM Term Term Term -- ~x{False:t;True:t}

  -- -- Nat
  -- | Nat                 -- Nat
  -- | Zer                 -- 0
  -- | Suc Term            -- ↑n
  -- | NatM Term Term Term -- ~x{0n:z;1n+:s}

  -- -- List
  -- | Lst Type            -- T[]
  -- | Nil                 -- []
  -- | Con Term Term       -- h<>t
  -- | LstM Term Term Term -- ~x{[]:n;<>:c}

  -- -- Enum
  -- | Enu [String]                   -- {@foo,@bar...}
  -- | Sym String                     -- @foo
  -- | EnuM Term [(String,Term)] Term -- ~x{@foo:f;@bar:b;...d}

  -- -- Numbers
  -- | Num NTyp           -- CHR | U64 | I64 | F64
  -- | Val NVal           -- 123 | +123 | +123.0
  -- | Op2 NOp2 Term Term -- x + y
  -- | Op1 NOp1 Term      -- !x

  -- -- Pair
  -- | Sig Type Type       -- ΣA.B
  -- | Tup Term Term       -- (a,b)
  -- | SigM Term Term      -- ~x{(,):f}

  -- -- Function
  -- | All Type Type              -- ∀A.B
  -- | Lam Name (Maybe Term) Body -- λx.f | λx:A . f
  -- | App Term Term              -- (f x)

  -- -- Equality
  -- | Eql Type Term Term -- T{a==b}
  -- | Rfl                -- {==}
  -- | EqlM Term Term     -- ~x{{==}:f}

  -- -- MetaVar
  -- | Met Name Type [Term] -- ?N:T{x0,x1,...}
  
  -- -- Hints
  -- | Ind Type -- ~~T
  -- | Frz Type -- ∅T

  -- -- Supperpositions
  -- | Era                 -- *
  -- | Sup Term Term Term  -- &L{a,b}
  -- | SupM Term Term Term -- ~x{&L{,}:f}

  -- -- Errors
  -- | Loc Span Term -- x
  -- | Rwt Term Term Term -- a → b ; x

  -- -- Logging
  -- | Log Term Term -- log s ; x

  -- -- Primitive
  -- | Pri PriF -- SOME_FUNC

  -- -- Sugars
  -- | Pat [Term] [Move] [Case] -- match x ... { with k=v ... ; case @A ...: F ; ... }
  -- | Frk Term Term Term       -- fork L:a else:b

-- NEW TERM TYPE:

-- Bend's Term Type
data Term
  -- Variables
  = Var Name Int -- x
  | Ref Name     -- x
  | Sub Term     -- x

  -- Definitions
  | Fix Name Body                   -- μx. f
  | Let Name (Maybe Term) Term Body -- !x : T = v; f

  -- Universe
  | Set -- Set

  -- Annotation
  | Chk Term Type -- x::t

  -- Empty
  | Emp  -- Empty
  | EmpM -- λ{}

  -- Unit
  | Uni            -- Unit
  | One            -- ()
  | UniM Term Term -- λ{():f}

  -- Bool
  | Bit            -- Bool
  | Bt0            -- False
  | Bt1            -- True
  | BitM Term Term -- λ{False:t;True:t}

  -- Nat
  | Nat            -- Nat
  | Zer            -- 0
  | Suc Term       -- ↑n
  | NatM Term Term -- λ{0n:z;1n+:s}

  -- List
  | Lst Type       -- T[]
  | Nil            -- []
  | Con Term Term  -- h<>t
  | LstM Term Term -- λ{[]:n;<>:c}

  -- Enum
  | Enu [String]              -- {&foo,&bar...}
  | Sym String                -- &foo
  | EnuM [(String,Term)] Term -- λ{&foo:f;&bar:b;...d}

  -- Numbers
  | Num NTyp           -- CHR | U64 | I64 | F64
  | Val NVal           -- 123 | +123 | +123.0
  | Op2 NOp2 Term Term -- x + y
  | Op1 NOp1 Term      -- !x

  -- Pair
  | Sig Type Type -- ΣA.B
  | Tup Term Term -- (a,b)
  | SigM Term     -- λ{(,):f}

  -- Function
  | All Type Type              -- ∀A.B
  | Lam Name (Maybe Term) Body -- λx.f | λx:A.f
  | App Term Term              -- (f x)

  -- Equality
  | Eql Type Term Term -- T{a==b}
  | Rfl                -- {==}
  | EqlM Term Term     -- λ{{==}:f}:T

  -- MetaVar
  | Met Name Type [Term] -- ?N:T{x0,x1,...}

  -- Supperpositions
  | Era                 -- *
  | Sup Term Term Term  -- &L{a,b}
  | SupM Term Term      -- λ{&L{,}:f}

  -- Errors
  | Loc Span Term -- x

  -- Logging
  | Log Term Term -- log s ; x

  -- Primitive
  | Pri PriF -- SOME_FUNC

  -- Sugars
  | Pat [Term] [Move] [Case] -- match x ... { with k=v ... ; case @A ...: F ; ... }
  | Frk Term Term Term       -- fork L:a else:b

-- # Changes:
-- 
-- ## Pattern-Matching is now done via λ-Matches:
-- 
-- All pattern-matching terms were replaced by λ-Match terms.
-- That means that, now, instead of:
--   ~ x { 0n:A 1n+:λp.B }
-- We write:
--   (λ{ 0n:A 1n+:λp.B } x)
-- I.e., the scrutinee has been moved out: 'App mat_fn scrutinee'.
-- On WHNF, instead of implementing rules like 'whnfNatM', we implement rules
-- like 'whnfAppNat' instead. The whnfApp rule will dispatch to the λ-matcher.
-- 
-- ## The Ind/Frz hints were completely removed.
--
-- We don't use these anymore, so, they were removed.
-- 
-- ## Rewrites have been refactored:
-- 
-- The Rwt constructor has been removed.
-- The Rewrite.hs file will also be removed.
-- Instead, when checking dependent eliminations like λ{ 0n:Z 1n+:S }, we will
-- substitute 0n and 1n+p on the *existing goal*, rather than using rewrite.
-- For example:
-- check λ{ 0n:Z 1n+:S } :: ∀n:Nat.P(n) =>
-- - check Z :: P(0n)
-- - check S :: ∀n:Nat.P(1n+n)
-- This removes the need for 'rewrite' on all checking rules, except for:
-- - λ{ {==}:R }
-- To amend that, we extend EqlM with an explicit motive:
-- - λ{ {==}:R } : P
-- 
-- ## Equality is now fully observational:
-- 
-- Previously, Equality had some observational flavor, because we allowed, in
-- the type-checker, for T{↑a == ↑b} to check as ↑T{a == b}, and similar. Now,
-- equality is truly observational, in the sense that it *reduces* to either
-- Unit or Empty. For example, Nat{0 == 0} reduces to Uni, and Nat{0 == 1}
-- reduces to empty.
-- 
-- ## Guarded Derefs replace Undo-Ugly
-- 
-- Previously, WHNF included an EvalLevel argument, with the goal of "undo'in
-- ugly forms". That functionality will be removed. Instead, we will include a
-- "Guarded Deref" function, which unrolls a ref against λ-cases, undo'ing on
-- demand when it gets stuck in a var. The WHNF will not receive a level
-- anymore, and the 'ugly' function will be removed.
-- 
-- ## New WHNF Reference:
-- 
-- The code below is the WHNF of Bend-in-Bend. The Haskell implementation should
-- align with it as closely as possible.
-- 
-- def whnf(term: Term) -> Term:
--   match term:
--     case @Ref{k, f, t}:
--       whnf_ref(k, f, t)
--     case @Let{T, v, f}:
--       whnf_let(T, v, f)
--     case @Fix{f}:
--       whnf_fix(f)
--     case @App{f, x}:
--       whnf_app(f, x)
--     case @Eql{t, a, b}:
--       whnf_eql(t, a, b)
--     case @Rwt{e, P, f}:
--       whnf_rwt(e, P, f)
--     case x:
--       x
-- 
-- def whnf_ref(k: String, f: Term, t: Term) -> Term:
--   deref(k, @LHS{0n, λk.k}, f)
-- 
-- def whnf_let(T: Term, v: Term, f: Term -> Term) -> Term:
--   whnf(f(v))
-- 
-- def whnf_fix(f: Term -> Term) -> Term:
--   whnf(f(whnf(@Fix{f})))
-- 
-- def whnf_app(f: Term, x: Term) -> Term:
--   match whnf(f):
--     with x
--     case @Lam{f}:
--       whnf(f(whnf(x)))
--     case @UniM{f}:
--       whnf_uni(x, f)
--     case @BitM{f, t}:
--       whnf_bit(x, f, t)
--     case @NatM{z, s}:
--       whnf_nat(x, z, s)
--     case @LstM{n, c}:
--       whnf_lst(x, n, c)
--     case @SigM{f}:
--       whnf_sig(x, f)
--     case f:
--       @App{f, x}
-- 
-- def whnf_uni(x: Term, f: Term) -> Term:
--   match whnf(x):
--     with f
--     case @One:
--       whnf(f)
--     case x:
--       @App{@UniM{f}, x}
-- 
-- def whnf_bit(x: Term, f: Term, t: Term) -> Term:
--   match whnf(x):
--     with f
--     with t
--     case @Bt0:
--       whnf(f)
--     case @Bt1:
--       whnf(t)
--     case x:
--       @App{@BitM{f, t}, x}
-- 
-- def whnf_nat(x: Term, z: Term, s: Term) -> Term:
--   match whnf(x):
--     with z
--     with s
--     case @Zer:
--       whnf(z)
--     case @Suc{n}:
--       whnf(@App{s, whnf(n)})
--     case x:
--       @App{@NatM{z, s}, x}
-- 
-- def whnf_lst(x: Term, n: Term, c: Term) -> Term:
--   match whnf(x):
--     with n
--     with c
--     case @Nil:
--       whnf(n)
--     case @Con{h, t}:
--       whnf(@App{@App{c, whnf(h)}, whnf(t)})
--     case x:
--       @App{@LstM{n, c}, x}
-- 
-- def whnf_sig(x: Term, f: Term) -> Term:
--   match whnf(x):
--     with f
--     case @Tup{a, b}:
--       whnf(@App{@App{f, whnf(a)}, whnf(b)})
--     case x:
--       @App{@SigM{f}, x}
-- 
-- def whnf_eql(T: Term, a: Term, b: Term) -> Term:
--   match whnf(T):
--     with a
--     with b
--     case @Uni:
--       match a b:
--         case @One @One:
--           @Uni
--         case a b:
--           @Eql{@Bit, a, b}
--     case @Bit:
--       match whnf(a) whnf(b):
--         case @Bt0 @Bt0:
--           @Uni
--         case @Bt1 @Bt1:
--           @Uni
--         case @Bt0 @Bt1:
--           @Emp
--         case @Bt1 @Bt0:
--           @Emp
--         case a b:
--           @Eql{@Bit, a, b}
--     case @Nat:
--       match whnf(a) whnf(b):
--         case @Zer @Zer:
--           @Uni
--         case @Zer @Suc{b}:
--           @Emp
--         case @Suc{a} @Zer:
--           @Emp
--         case @Suc{a} @Suc{b}:
--           whnf(@Eql{@Nat, a, b})
--         case a b:
--           @Eql{@Nat, a, b}
--     case @Lst{T}:
--       match whnf(a) whnf(b):
--         case @Nil @Nil:
--           @Uni
--         case @Nil @Con{bh,bt}:
--           @Emp
--         case @Con{ah,at} @Nil:
--           @Emp
--         case @Con{ah,at} @Con{bh,bt}:
--           whnf(@Sig{@Eql{T, ah, bh}, @Lam{λ_. @Eql{@Lst{T}, at, bt}}})
--         case a b:
--           @Eql{@Lst{T}, a, b}
--     case @Sig{X,Y}:
--       match whnf(a) whnf(b):
--         case @Tup{ax,ay} @Tup{bx,by}:
--           whnf(@Sig{@Eql{X, ax, bx}, @Lam{λ_. @Eql{@App{Y, ax}, ay, by}}})
--         case a b:
--           @Eql{@Sig{X,Y}, a, b}
--     case @All{X,Y}:
--       @All{X, @Lam{λx. @Eql{@App{Y,x}, @App{a,x}, @App{b,x}}}}
--     case T:
--       @Eql{T, a, b}
-- 
-- def whnf_rwt(e: Term, P: Term, f: Term) -> Term:
--   match whnf(e):
--     with P
--     with f
--     case @Uni:
--       whnf(f)
--     case @Emp:
--       *
--     case e:
--       @Rwt{e, P, f}
-- 
-- # Guarded Deref
-- # -------------
-- # Converts the Ref's body into a "guarded matcher" that eliminates received args
-- # until it either succeeds, or gets stuck against a var. This emulates Agda-like
-- # clauses, giving us recursive recursive Refs that don't unroll infinitely.
-- 
-- def deref(k: String, lhs: LHS, body: Term) -> Term:
--   #log String/flat(["deref ", show(0n,F), " - ", show(0n,body)])
--   match body:
--     with k
--     with lhs
--     case @EmpM:
--       @Lam{λx. deref_undo(k, lhs, @EmpM, x)} # FIXME: review
--     case @UniM{f}:
--       @Lam{λx.
--         match x:
--           case @One:
--             deref(k, lhs_ctr(lhs, 0n, @One), f)
--           case x:
--             deref_undo(k, lhs, @UniM{f}, x)}
--     case @BitM{f,t}:
--       @Lam{λx.
--         match x:
--           case @Bt0:
--             deref(k, lhs_ctr(lhs, 0n, @Bt0), f)
--           case @Bt1:
--             deref(k, lhs_ctr(lhs, 0n, @Bt1), t)
--           case x:
--             deref_undo(k, lhs, @BitM{f,t}, x)}
--     case @NatM{z,s}:
--       @Lam{λx.
--         match x:
--           case @Zer:
--             deref(k, lhs_ctr(lhs, 0n, @Zer), z)
--           case @Suc{xp}:
--             @App{deref(k, lhs_ctr(lhs, 1n, λp.@Suc{p}), s), xp}
--           case x:
--             deref_undo(k, lhs, @NatM{z,s}, x)}
--     case @LstM{n,c}:
--       @Lam{λx.
--         match x:
--           case @Nil:
--             deref(k, lhs_ctr(lhs, 0n, @Nil), n)
--           case @Con{h,t}:
--             @App{@App{deref(k, lhs_ctr(lhs, 2n, λh.λt.@Con{h,t}), c), h}, t}
--           case x:
--             deref_undo(k, lhs, @LstM{n,c}, x)}
--     case @SigM{f}:
--       @Lam{λx.
--         match x:
--           case @Tup{a,b}:
--             @App{@App{deref(k, lhs_ctr(lhs, 2n, λa.λb.@Tup{a,b}), f), a}, b}
--           case x:
--             deref_undo(k, lhs, @SigM{f}, x)}
--     case @Lam{f}: # FIXME: can we avoid cloning 'x' here?
--       @Lam{λx. deref(k, lhs_ctr(lhs, 0n, x), f(x))}
--     case body:
--       body
-- 
-- def deref_undo(k: String, lhs: LHS, body: Term, x: Term) -> Term:
--   @LHS{K,L} = lhs
--   match K:
--     case 0n:
--       @App{L(@Nam{k}), x}
--     case 1n+K:
--       deref(k, @LHS{K, L(x)}, body)
-- 
-- type LHS:
--   case @LHS:
--     K: Nat
--     L: Term -> Arg<K>
-- 
-- def lhs_ctr_new(L: Term -> Term, N: Nat, ctr: Arg<N>) -> Term -> Arg<N>:
--   match N:
--     with L
--     with ctr
--     case 0n:
--       λk. @App{L(k), ctr}
--     case 1n+Np:
--       λx. lhs_ctr_new(L, Np, ctr(x))
-- 
-- def lhs_ctr_ext(K: Nat, L: Term -> Arg<1n+K>, N: Nat, ctr: Arg<N>) -> Arg<1n+Nat/add(N,K)>:
--   match N:
--     with K
--     with L
--     with ctr
--     case 0n:
--       L(ctr)
--     case 1n+Np:
--       λx. lhs_ctr_ext(K, L, Np, ctr(x))
-- 
-- def lhs_ctr(lhs: LHS, N: Nat, ctr: Arg<N>) -> LHS:
--   @LHS{K,L} = lhs
--   match K:
--     with L
--     with N
--     with ctr
--     case 0n:
--       @LHS{N, lhs_ctr_new(L, N, ctr)}
--     case 1n+K:
--       @LHS{Nat/add(N,K), lhs_ctr_ext(K, L, N, ctr)}
-- 
-- def lhs_to_list(lhs: LHS) -> Term[]:
--   @LHS{K,L} = lhs
--   match K:
--     case 0n:
--       get_args(L(@Emp), [])
--     case 1n+K:
--       [] # won't happen
-- 
-- Note: since Haskell doesn't have dependent types, in order to implement the
-- LHS type and functions, we use Term lambdas instead of native lambdas. That
-- is, the LHS type will hold an Int and a Term, and, whenever we used a native
-- lambda previously (like `lhs_ctr(lhs, 2n, λa.λb.@Tup{a,b})`), we will simply
-- use a Term lambda instead (like `lhsCtr lhs 2 (Lam(\a->Lam(\b->Tup a b)))`)
-- This will simplify type-checking, as we'll avoid GADTs and similar.

-- Book of Definitions
type Inj  = Bool -- "is injective" flag. improves pretty printing
type Defn = (Inj, Term, Type)
data Book = Book (M.Map Name Defn)

-- Substitution Map
type Subs = [(Term,Term)]

-- Context (new type)
data Ctx = Ctx [(Name,Term,Term)]

-- Error Location (NEW TYPE)
data Span = Span
  { spanBeg :: (Int,Int)
  , spanEnd :: (Int,Int)
  , spanSrc :: String -- original file
  , spanPth :: FilePath -- original file path
  }

data Error
  = CantInfer Span Ctx
  | Undefined Span Ctx Name
  | TypeMismatch Span Ctx Term Term
  | TermMismatch Span Ctx Term Term
  | IncompleteMatch Span Ctx

data Result a
  = Done a
  | Fail Error

instance Functor Result where
  fmap f (Done a) = Done (f a)
  fmap _ (Fail e) = Fail e

instance Applicative Result where
  pure              = Done
  Done f <*> Done a = Done (f a)
  Fail e <*> _      = Fail e
  _      <*> Fail e = Fail e

instance Monad Result where
  Done a >>= f = f a
  Fail e >>= _ = Fail e

instance Show Term where
  show (Var k i)      = k -- ++ "^" ++ show i
  show (Ref k)        = k
  show (Sub t)        = show t
  show (Fix k f)      = "μ" ++ k ++ ". " ++ show (f (Var k 0))
  show (Let k t v f)  = case t of
    Just t  -> "!" ++ k ++ " : " ++ show t ++ " = " ++ show v ++ ";" ++ show (f (Var k 0))
    Nothing -> "!" ++ k ++                    " = " ++ show v ++ ";" ++ show (f (Var k 0))
  show (Set)          = "Set"
  show (Chk x t)      = "(" ++ show x ++ "::" ++ show t ++ ")"
  show (Emp)          = "Empty"
  show (EmpM)         = "λ{}"
  show (Uni)          = "Unit"
  show (One)          = "()"
  show (UniM x f)     = "λ{():" ++ show x ++ "." ++ show f ++ "}"
  show (Bit)          = "Bool"
  show (Bt0)          = "False"
  show (Bt1)          = "True"
  show (BitM f t)     = "λ{False:" ++ show f ++ ";True:" ++ show t ++ "}"
  show (Nat)          = "Nat"
  show (Zer)          = "0n"
  show (Suc n)        = "1n+" ++ show n
  show (NatM z s)     = "λ{0n:" ++ show z ++ ";1n+:" ++ show s ++ "}"
  show (Lst t)        = show t ++ "[]"
  show (Nil)          = "[]"
  show (Con h t)      = fromMaybe (show h ++ "<>" ++ show t) (prettyStr (Con h t))
  show (LstM n c)     = "λ{[]:" ++ show n ++ ";<>:" ++ show c ++ "}"
  show (Enu s)        = "enum{" ++ intercalate "," (map (\x -> "&" ++ x) s) ++ "}"
  show (Sym s)        = "&" ++ s
  show (EnuM c e)     = "λ{" ++ intercalate ";" (map (\(s,t) -> "&" ++ s ++ ":" ++ show t) c) ++ ";" ++ show e ++ "}"
  show (Sig a b) = case b of
      Lam "_" t f -> showArg a ++ " & " ++ showCodomain (f (Var "_" 0))
      Lam k t f   -> "Σ" ++ k ++ ":" ++ showArg a ++ ". " ++ show (f (Var k 0))
      _           -> "Σ" ++ showArg a ++ ". " ++ show b
    where
      showArg t = case t of
          All{} -> "(" ++ show t ++ ")"
          Sig{} -> "(" ++ show t ++ ")"
          _     -> show t
      showCodomain t = case t of
          Sig _ (Lam k _ _) | k /= "_" -> "(" ++ show t ++ ")"
          _                           -> show t
  show tup@(Tup _ _)  = fromMaybe ("(" ++ intercalate "," (map show (flattenTup tup)) ++ ")") (prettyCtr tup)
  show (SigM f)       = "λ{(,):" ++ show f ++ "}"
  show (All a b) = case b of
      Lam "_" t f -> showArg a ++ " -> " ++ showCodomain (f (Var "_" 0))
      Lam k t f   -> "∀" ++ k ++ ":" ++ showArg a ++ ". " ++ show (f (Var k 0))
      _           -> "∀" ++ showArg a ++ ". " ++ show b
    where
      showArg t = case t of
          All{} -> "(" ++ show t ++ ")"
          Sig{} -> "(" ++ show t ++ ")"
          _     -> show t
      showCodomain t = case t of
          All _ (Lam k _ _) | k /= "_"  -> "(" ++ show t ++ ")"
          _                           -> show t
  show (Lam k t f)      = case t of
    Just t  -> "λ" ++ k ++ " : " ++ show t ++ " . " ++ show (f (Var k 0))
    Nothing -> "λ" ++ k ++ ". " ++ show (f (Var k 0))
  show app@(App _ _)  = fnStr ++ "(" ++ intercalate "," (map show args) ++ ")" where
           (fn, args) = collectApps app []
           fnStr      = case cut fn of
              Var k i -> show (Var k i)
              Ref k   -> show (Ref k)
              fn      -> "(" ++ show fn ++ ")"
  show (Eql t a b)     = case t of
    (Sig _ _) -> "(" ++ show t ++ ")" ++ "{" ++ show a ++ "==" ++ show b ++ "}"
    (All _ _) -> "(" ++ show t ++ ")" ++ "{" ++ show a ++ "==" ++ show b ++ "}"
    _         ->        show t ++        "{" ++ show a ++ "==" ++ show b ++ "}"
  show (Rfl)           = "{==}"
  show (EqlM p f)      = "λ{{==}:" ++ show f ++ "}:" ++ show p
  show (Loc _ t)       = show t
  show (Era)           = "*"
  show (Sup l a b)     = "&" ++ show l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (SupM l f)      = "λ{&" ++ show l ++ "{,}:" ++ show f ++ "}"
  show (Frk l a b)     = "fork " ++ show l ++ ":" ++ show a ++ " else:" ++ show b
  show (Met n t ctx)   = "?" ++ n ++ ":" ++ show t ++ "{" ++ intercalate "," (map show ctx) ++ "}"
  show (Log s x)       = "log " ++ show s ++ " " ++ show x
  show (Pri p)         = pri p where
    pri U64_TO_CHAR    = "U64_TO_CHAR"
    pri CHAR_TO_U64    = "CHAR_TO_U64"
  show (Num U64_T)     = "U64"
  show (Num I64_T)     = "I64"
  show (Num F64_T)     = "F64"
  show (Num CHR_T)     = "Char"
  show (Val (U64_V n)) = show n
  show (Val (I64_V n)) = if n >= 0 then "+" ++ show n else show n
  show (Val (F64_V n)) = show n
  show (Val (CHR_V c)) = "'" ++ showChar c ++ "'" where
         showChar '\n' = "\\n"
         showChar '\t' = "\\t"
         showChar '\r' = "\\r"
         showChar '\0' = "\\0"
         showChar '\\' = "\\\\"
         showChar '\'' = "\\'"
         showChar c    = [c]
  show (Op2 ADD a b)   = "(" ++ show a ++ " + " ++ show b ++ ")"
  show (Op2 SUB a b)   = "(" ++ show a ++ " - " ++ show b ++ ")"
  show (Op2 MUL a b)   = "(" ++ show a ++ " * " ++ show b ++ ")"
  show (Op2 DIV a b)   = "(" ++ show a ++ " / " ++ show b ++ ")"
  show (Op2 MOD a b)   = "(" ++ show a ++ " % " ++ show b ++ ")"
  show (Op2 EQL a b)   = "(" ++ show a ++ " == " ++ show b ++ ")"
  show (Op2 NEQ a b)   = "(" ++ show a ++ " !== " ++ show b ++ ")"
  show (Op2 LST a b)   = "(" ++ show a ++ " < " ++ show b ++ ")"
  show (Op2 GRT a b)   = "(" ++ show a ++ " > " ++ show b ++ ")"
  show (Op2 LEQ a b)   = "(" ++ show a ++ " <= " ++ show b ++ ")"
  show (Op2 GEQ a b)   = "(" ++ show a ++ " >= " ++ show b ++ ")"
  show (Op2 AND a b)   = "(" ++ show a ++ " && " ++ show b ++ ")"
  show (Op2 OR a b)    = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Op2 XOR a b)   = "(" ++ show a ++ " ^ " ++ show b ++ ")"
  show (Op2 SHL a b)   = "(" ++ show a ++ " << " ++ show b ++ ")"
  show (Op2 SHR a b)   = "(" ++ show a ++ " >> " ++ show b ++ ")"
  show (Op2 POW a b)   = "(" ++ show a ++ " ** " ++ show b ++ ")"
  show (Op1 NOT a)     = "(not " ++ show a ++ ")"
  show (Op1 NEG a)     = "(-" ++ show a ++ ")"
  show (Pat t m c)     = "match " ++ unwords (map show t) ++ " {" ++ showMoves ++ showCases ++ " }" where
             showMoves = if null m then "" else " with " ++ intercalate " with " (map mv m) where
               mv(k,x) = k ++ "=" ++ show x
             showCases = if null c then "" else " " ++ intercalate " " (map cs c) where
               cs(p,x) = "case " ++ unwords (map showPat p) ++ ": " ++ show x
             showPat p = "(" ++ show p ++ ")"

instance Show Book where
  show (Book defs) = unlines (map defn (M.toList defs))
    where defn (k,(_,x,t)) = k ++ " : " ++ show t ++ " = " ++ show x

instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m "
    ++ "\x1b[2m(line "++show (fst $ spanBeg span)++ ", column "++show (snd $ spanBeg span)++")\x1b[0m\n"
    ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

instance Show Error where
  show (CantInfer span ctx) = 
    "\x1b[1mCantInfer:\x1b[0m" ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (Undefined span ctx name) = 
    "\x1b[1mUndefined:\x1b[0m " ++ name ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (TypeMismatch span ctx goal typ) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- Goal: " ++ show goal ++ 
    "\n- Type: " ++ show typ ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (TermMismatch span ctx a b) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- " ++ show a ++ 
    "\n- " ++ show b ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (IncompleteMatch span ctx) = 
    "\x1b[1mIncompleteMatch:\x1b[0m" ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span

instance Show Ctx where
  show (Ctx ctx)
    | null lines = ""
    | otherwise  = init (unlines lines)
    where
      lines = map snd (reverse (clean S.empty (reverse (map showAnn ctx))))

      showAnn :: (Name,Term,Term) -> (Name,String)
      showAnn (k,_,t) = (k, "- " ++ k ++ " : " ++ show t)
    
      clean :: S.Set Name -> [(Name,String)] -> [(Name,String)]
      clean _    []                             = []
      clean seen ((n,l):xs) | n `S.member` seen = clean seen xs
                            | take 1 n == "_"   = clean seen xs
                            | otherwise         = (n,l) : clean (S.insert n seen) xs

-- Utils
-- -----

deref :: Book -> Name -> Maybe Defn
deref (Book defs) name = M.lookup name defs

cut :: Term -> Term
cut (Loc _ t) = cut t
cut (Chk x _) = cut x
cut t         = t

unlam :: Name -> Int -> (Term -> Term) -> Term
unlam k d f = f (Var k d)

collectArgs :: Term -> ([(String, Term)], Term)
collectArgs = go [] where
  go acc (Loc _ t)            = go acc t
  go acc (All t (Lam k ty f)) = go (acc ++ [(k, t)]) (f (Var k 0))
  go acc goal                 = (acc, goal)

collectApps :: Term -> [Term] -> (Term, [Term])
collectApps (cut -> App f x) args = collectApps f (x:args)
collectApps f                args = (f, args)

noSpan :: Span
noSpan = Span (0,0) (0,0) "" ""

flattenTup :: Term -> [Term]
flattenTup (Tup l r) = l : flattenTup r
flattenTup t         = [t]

lastElem :: Term -> Maybe Term
lastElem (Tup _ r) = lastElem r
lastElem t         = Just t

prettyCtr :: Term -> Maybe String
prettyCtr (Tup (Sym name) rest) = 
  case lastElem rest of
    Just One -> Just ("@" ++ name ++ "{" ++ intercalate "," (map show (init (flattenTup rest))) ++ "}")
    _        -> Nothing
prettyCtr _ = Nothing

prettyStr :: Term -> Maybe String
prettyStr = go [] where
  go :: [Char] -> Term -> Maybe String
  go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
  go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
  go acc (Loc _ t)                  = go acc t
  go _   _                          = Nothing

-- | Returns the free variables in a term by name.
freeVars :: S.Set Name -> Term -> S.Set Name
freeVars ctx tm = case tm of
  Var n _     -> if n `S.member` ctx then S.empty else S.singleton n
  Sub t       -> freeVars ctx t
  Fix n f     -> freeVars (S.insert n ctx) (f (Var n 0))
  Let k t v f -> S.unions [foldMap (freeVars ctx) t, freeVars ctx v, freeVars (S.insert k ctx) (f (Var k 0))]
  Chk v t     -> S.union (freeVars ctx v) (freeVars ctx t)
  EmpM        -> S.empty
  UniM x f    -> S.union (freeVars ctx x) (freeVars ctx f)
  BitM f t    -> S.union (freeVars ctx f) (freeVars ctx t)
  Suc n       -> freeVars ctx n
  NatM z s    -> S.union (freeVars ctx z) (freeVars ctx s)
  Lst t       -> freeVars ctx t
  Con h t     -> S.union (freeVars ctx h) (freeVars ctx t)
  LstM n c    -> S.union (freeVars ctx n) (freeVars ctx c)
  EnuM c e    -> S.union (S.unions (map (freeVars ctx . snd) c)) (freeVars ctx e)
  Op2 _ a b   -> S.union (freeVars ctx a) (freeVars ctx b)
  Op1 _ a     -> freeVars ctx a
  Sig a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  Tup a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  SigM f      -> freeVars ctx f
  All a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  Lam n t f   -> S.union (freeVars (S.insert n ctx) (f (Var n 0))) (foldMap (freeVars ctx) t)
  App f x     -> S.union (freeVars ctx f) (freeVars ctx x)
  Eql t a b   -> S.unions [freeVars ctx t, freeVars ctx a, freeVars ctx b]
  EqlM p f    -> S.union (freeVars ctx p) (freeVars ctx f)
  Met _ t c   -> S.unions (freeVars ctx t : map (freeVars ctx) c)
  Sup _ a b   -> S.union (freeVars ctx a) (freeVars ctx b)
  SupM l f    -> S.union (freeVars ctx l) (freeVars ctx f)
  Frk l a b   -> S.unions [freeVars ctx l, freeVars ctx a, freeVars ctx b]
  Log s x     -> S.union (freeVars ctx s) (freeVars ctx x)
  Loc _ t     -> freeVars ctx t
  Pat s m c   -> S.unions ((map (freeVars ctx) s) ++ (map (\(_,m) -> freeVars ctx m) m) ++ (map (\(_,c) -> freeVars ctx c) c))
  _           -> S.empty

-- | Check if a term contains a Metavar
hasMet :: Term -> Bool
hasMet term = case term of
  Met {} -> True
  Sub t -> hasMet t
  Fix _ f -> hasMet (f (Var "" 0))
  Let k t v f -> case t of
    Just t  -> hasMet t || hasMet v || hasMet (f (Var k 0))
    Nothing -> hasMet v || hasMet (f (Var k 0))
  Chk x t -> hasMet x || hasMet t
  EmpM -> False
  UniM x f -> hasMet x || hasMet f
  BitM f t -> hasMet f || hasMet t
  Suc n -> hasMet n
  NatM z s -> hasMet z || hasMet s
  Lst t -> hasMet t
  Con h t -> hasMet h || hasMet t
  LstM n c -> hasMet n || hasMet c
  EnuM cs e -> any (hasMet . snd) cs || hasMet e
  Op2 _ a b -> hasMet a || hasMet b
  Op1 _ a -> hasMet a
  Sig a b -> hasMet a || hasMet b
  Tup a b -> hasMet a || hasMet b
  SigM f -> hasMet f
  All a b -> hasMet a || hasMet b
  Lam _ t f -> maybe False hasMet t || hasMet (f (Var "" 0))
  App f x -> hasMet f || hasMet x
  Eql t a b -> hasMet t || hasMet a || hasMet b
  EqlM p f -> hasMet p || hasMet f
  Sup _ a b -> hasMet a || hasMet b
  SupM l f -> hasMet l || hasMet f
  Loc _ t -> hasMet t
  Log s x -> hasMet s || hasMet x
  Pat s m c -> any hasMet s || any (hasMet . snd) m || any (\(p,b) -> any hasMet p || hasMet b) c
  Frk l a b -> hasMet l || hasMet a || hasMet b
  _ -> False
