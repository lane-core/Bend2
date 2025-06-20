module Core.Type where

import Data.List (intercalate)
import Debug.Trace
import Highlight (highlightError)
import qualified Data.Map as M
import qualified Data.Set as S


data Bits = O Bits | I Bits | E deriving Show
type Name = String
type Body = Term -> Term
type Case = ([Term], Term)
type Move = (String, Term)
type Type = Term

-- Bend's Term Type
data Term
  -- Variables
  = Var Name Int -- x
  | Ref Name     -- x
  | Sub Term     -- x

  -- Definitions
  | Fix Name Body -- μx. f
  | Let Term Term -- !v; f

  -- Universe
  | Set -- Set

  -- Annotation
  | Ann Term Type -- <x:t>
  | Chk Term Type -- x::t

  -- Empty
  | Emp -- Empty
  | Efq -- λ{}

  -- Unit
  | Uni      -- Unit
  | One      -- ()
  | Use Term -- λ{():f}

  -- Bool
  | Bit           -- Bool
  | Bt0           -- False
  | Bt1           -- True
  | Bif Term Term -- λ{False:f;True:t}

  -- Nat
  | Nat           -- Nat
  | Zer           -- 0
  | Suc Term      -- ↑n
  | Swi Term Term -- λ{0:z;+:s}

  -- List
  | Lst Type      -- T[]
  | Nil           -- []
  | Con Term Term -- h<>t
  | Mat Term Term -- λ{[]:n;<>:c}

  -- Enum
  | Enu [String]        -- {'foo','bar'...}
  | Sym String          -- 'foo'
  | Cse [(String,Term)] -- λ{'foo':f;'bar':b;...}

  -- Pair
  | Sig Type Type -- ΣA.B
  | Tup Term Term -- (a,b)
  | Get Term      -- λ{(,):f}

  -- Function
  | All Type Type -- ∀A.B
  | Lam Name Body -- λx.f
  | App Term Term -- (f x)

  -- Equality
  | Eql Type Term Term -- T{a==b}
  | Rfl                -- {=}
  | Rwt Term           -- λ{{=}:f}

  -- MetaVar
  | Met Int Type [Term] -- ?N:T{x0,x1,...}
  
  -- Hints
  | Ind Type -- ~T
  | Frz Type -- ∅T

  -- Supperpositions
  | Era               -- *
  | Sup Int Term Term -- &L{a,b}

  -- Errors
  | Loc Span Term -- (NEW CONSTRUCTOR)

  -- Pattern-Match
  -- match x y ... {
  --   with a=r with b=s ...
  --   case (A ...) (B ...): ...
  --   case (C ...) (D ...): ...
  -- }
  | Pat [Term] [Move] [Case]

-- Book of Definitions
type Inj  = Bool -- "is injective" flag. improves pretty printing
type Defn = (Inj, Term, Type)
data Book = Book (M.Map Name Defn)

-- Error Location (NEW TYPE)
data Span = Span
  { spanBeg :: (Int,Int)
  , spanEnd :: (Int,Int)
  , spanSrc :: String -- original file
  }

data Error
  = CantInfer Span Term
  | TypeMismatch Span Term Term Term
  | TermMismatch Span Term Term Term

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
  show = unwrap . go where
    go (Var k i)      = k
    go (Ref k)        = k
    go (Sub t)        = error "unreachable"
    go (Fix k f)      = "μ" ++ k ++ "." ++ go (f (Var k 0))
    -- go (Fix k f)      = k
    go (Let v f)      = "!" ++ go v ++ ";" ++ go f
    go (Set)          = "Set"
    go (Ann x t)      = "<" ++ go x ++ ":" ++ go t ++ ">"
    go (Chk x t)      = "(" ++ go x ++ "::" ++ go t ++ ")"
    go (Emp)          = "⊥"
    go (Efq)          = "λ{}"
    go (Uni)          = "Unit"
    go (One)          = "()"
    go (Use f)        = "λ{():" ++ go f ++ "}"
    go (Bit)          = "Bool"
    go (Bt0)          = "False"
    go (Bt1)          = "True"
    go (Bif f t)      = "λ{False:" ++ go f ++ ";True:" ++ go t ++ "}"
    go (Nat)          = "Nat"
    go (Zer)          = "0"
    go (Suc n)        = "↑" ++ go n
    go (Swi z s)      = "λ{0:" ++ go z ++ ";+:" ++ go s ++ "}"
    go (Lst t)        = go t ++ "[]"
    go (Nil)          = "[]"
    go (Con h t)      = go h ++ "<>" ++ go t
    go (Mat n c)      = "λ{[]:" ++ go n ++ ";<>:" ++ go c ++ "}"
    go (Enu s)        = "{" ++ intercalate "," (map (\x -> "@" ++ x) s) ++ "}"
    go (Sym s)        = "@" ++ s
    go (Cse c)        = "λ{" ++ intercalate ";" (map (\(s,t) -> "@" ++ s ++ ":" ++ go t) c) ++ "}"
    go (Sig a b)      = sig a b where
      sig a (Lam "_" f) = go a ++ "&" ++ go (f (Var "_" 0))
      sig a (Lam k f)   = "Σ" ++ k ++ ":" ++ go a ++ "." ++ go (f (Var k 0))
      sig a b           = "Σ" ++ go a ++ "." ++ go b
    go (Tup a b)      = "(" ++ go a ++ "," ++ unwrap (go b) ++ ")"
    go (Get f)        = "λ{(,):" ++ go f ++ "}"
    go (All a b)      = all a b where
      all a (Lam "_" f) = go a ++ "→" ++ go (f (Var "_" 0))
      all a (Lam k f)   = "∀" ++ k ++ ":" ++ go a ++ "." ++ go (f (Var k 0))
      all a b           = "∀" ++ go a ++ "." ++ go b
    go (Lam k f)      = "λ" ++ k ++ "." ++ go (f (Var k 0))
    go app@(App _ _)  = "(" ++ fnStr ++ "(" ++ intercalate "," (map go args) ++ ")" ++ ")" where
      (fn, args) = collectApps app []
      fnStr      = unwrap (go fn)
    go (Eql t a b)    = go t ++ "{" ++ go a ++ "==" ++ go b ++ "}"
    go (Rfl)          = "{==}"
    go (Rwt f)        = "λ{{==}:" ++ go f ++ "}"
    go (Ind t)        = "~{" ++ go t ++ "}"
    go (Frz t)        = "∅" ++ go t
    go (Loc _ t)      = go t
    go (Era)          = "*"
    go (Sup l a b)    = "&" ++ show l ++ "{" ++ go a ++ "," ++ go b ++ "}"
    go (Met _ _ _)    = "?"
    go (Pat terms moves cases) = "match " ++ unwords (map go terms) ++ " {" ++ goMoves ++ goCases ++ "}" where
      goMoves = if null moves then "" else " with " ++ intercalate " with " (map goMove moves) where
        goMove (name, term) = name ++ "=" ++ go term
      goCases = if null cases then "" else " " ++ intercalate " " (map goCase cases) where
        goCase (pats, term) = "case " ++ unwords (map goPat pats) ++ ": " ++ go term
      goPat pat = "(" ++ go pat ++ ")"

instance Show Book where
  show (Book defs) = "Book {" ++ intercalate ", " (map defn (M.toList defs)) ++ "}"
    where defn (k,(_,x,t)) = k ++ " : " ++ show x ++ " = " ++ show t

instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m "
    ++ "\x1b[2m(line "++show (fst $ spanBeg span)++ ", column "++show (snd $ spanBeg span)++")\x1b[0m\n"
    ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

instance Show Error where
  show (CantInfer span ctx) = 
    "\x1b[1mCantInfer:\x1b[0m" ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ showContext ctx ++
    show span
  show (TypeMismatch span ctx goal typp) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- Goal: " ++ show goal ++ 
    "\n- Type: " ++ show typp ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ showContext ctx ++
    show span
  show (TermMismatch span ctx a b) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- " ++ show a ++ 
    "\n- " ++ show b ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ showContext ctx ++
    show span

showContext :: Term -> String
showContext ctx = init (unlines (map snd (reverse (dedup S.empty (reverse (go ctx [])))))) where

  go :: Term -> [(Name, String)] -> [(Name, String)]
  go (Let v (Lam k f)) acc = case v of
    (Chk _ ty) -> go (f (Var k 0)) (acc ++ [(k, "- " ++ k ++ " : " ++ show ty)])
    ty         -> go (f (Var k 0)) (acc ++ [(k, "- " ++ k)])
  go term acc = acc ++ [("", "\x1b[1mExpression:\x1b[0m\n- " ++ show term)]

  dedup :: S.Set Name -> [(Name,String)] -> [(Name,String)]
  dedup _    []                             = []
  dedup seen ((n,l):xs) | n `S.member` seen = dedup seen xs
                        | take 1 n == "_"   = dedup seen xs
                        | otherwise         = (n,l) : dedup (S.insert n seen) xs

-- Utils
-- -----

deref :: Book -> Name -> Maybe Defn
deref (Book defs) name = M.lookup name defs

-- Strip Loc wrappers
strip :: Term -> Term
strip (Loc _ t) = strip t
strip t         = t

collectArgs :: Term -> ([(String, Term)], Term)
collectArgs = go [] where
  go acc (Loc _ t)         = go acc t
  go acc (All t (Lam k f)) = go (acc ++ [(k, t)]) (f (Var k 0))
  go acc goal              = (acc, goal)

collectApps :: Term -> [Term] -> (Term, [Term])
collectApps (App f x) args = collectApps f (x:args)
collectApps f         args = (f, args)

natToInt :: Term -> Maybe Int
natToInt Zer       = Just 0
natToInt (Suc n)   = fmap (+1) (natToInt n)
natToInt (Loc _ t) = natToInt t
natToInt _         = Nothing

unwrap :: String -> String
unwrap "()"        = "()"
unwrap ('(' : txt) = init txt
unwrap txt         = txt

noSpan :: Span
noSpan = Span (0,0) (0,0) ""
