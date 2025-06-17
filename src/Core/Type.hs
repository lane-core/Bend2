-- NOTE: previously, this language did not feature global definitions. instead,
-- we provided a syntax sugar, 'def x : T = val', that desugared to a 'let',
-- allowing users to handle multiple definitions in the same file. this worked,
-- but was contrived and sub-optimal. our goal now is to implement proper global
-- definitions. to do so, we will introduce a new type, Book, which includes a
-- map from names to top-level definitions (Term,Type). then, many files will
-- require change:
-- Bind.hs: must include a bindBook function, which binds all Term/Types on
-- Book. when a variable is unbound, turn it into a Ref (instead of a Var).
-- Check.hs: functions must receive the Book after the 'd' argument, so that it
-- can be passed to equal, whnf, etc. also include a checkBook function, which
-- type-checks all terms of a Book.
-- Equal.hs: must receive Book after the 'd' argument, to pass to whnf
-- Normal.hs: must receive Book after the 'd' argument, to pass to whnf
-- Parse.hs: the old 'def' parser must be removed. we must add a parseBook
-- parser, which parses a series of def's (similar to the old 'def'), and
-- returns a Book.  we must include doParseBook and doReadBook functions for
-- convenience. note that the parser state must remain the same.
-- Pretty.hs: must include a prettifier for the book
-- Rewrite.hs: must receive Book after the 'd' argument
-- Type.hs: must include a Show instance for Book. also include a 'deref'
-- function to get a Maybe (Term,Type) from the Book.
-- WHNF.hs: must receive a Book. then, Ref's must be expanded to the respective
-- value on the book. this must be handled exactly like Fix: we only expand when
-- the Ref is on the function position of an application (i.e., whnfAppRef), and
-- only when lv=1.
-- files on NeoGen/: change as little as possible to make it compile. leave
-- TODO's if needed.
-- app/Main.hs: update the commands so that, when we load a file, we will parse
-- a Book (instead of a single Term). then, to run, we run the 'main'
-- definition. to check, we checkBook the whole book.
-- this isn't an extensive list; there might be some TODO's or small things I'm
-- missing, but the overall idea is here.

module Core.Type where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (intercalate)
import Debug.Trace

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
  | Emp -- ⊥
  | Efq -- λ{}

  -- Unit
  | Uni      -- ⊤
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

  -- Pattern-Match
  -- match x y ...:
  --   with a=r with b=s ...
  --   case (A ...) (B ...): ...
  --   case (C ...) (D ...): ...
  | Pat [Term] [Move] [Case]

-- New Types ↓
type Defn = (Term,Type)
data Book = Book (M.Map Name Defn)

instance Show Book where
  show (Book defs) = "Book {" ++ intercalate ", " entries ++ "}"
    where entries = map showDefn (M.toList defs)
          showDefn (name, (term, typ)) = name ++ " : " ++ show typ ++ " = " ++ show term

-- Get a definition from the Book
deref :: Book -> Name -> Maybe Defn
deref (Book defs) name = M.lookup name defs

instance Show Term where
  show (Var k i)      = k
  show (Ref k)        = k
  show (Sub t)        = error "unreachable"
  -- show (Fix k f)      = "μ" ++ k ++ "." ++ show (f (Var k 0))
  show (Fix k f)      = k
  show (Let v f)      = "!" ++ show v ++ ";" ++ show f
  show (Set)          = "Set"
  show (Ann x t)      = "<" ++ show x ++ ":" ++ show t ++ ">"
  show (Chk x t)      = "(" ++ show x ++ "::" ++ show t ++ ")"
  show (Emp)          = "⊥"
  show (Efq)          = "λ{}"
  show (Uni)          = "⊤"
  show (One)          = "()"
  show (Use f)        = "λ{():" ++ show f ++ "}"
  show (Bit)          = "Bool"
  show (Bt0)          = "False"
  show (Bt1)          = "True"
  show (Bif f t)      = "λ{False:" ++ show f ++ ";True:" ++ show t ++ "}"
  show (Nat)          = "Nat"
  show (Zer)          = "0"
  show (Suc n)        = "↑" ++ show n
  show (Swi z s)      = "λ{0:" ++ show z ++ ";+:" ++ show s ++ "}"
  show (Lst t)        = show t ++ "[]"
  show (Nil)          = "[]"
  show (Con h t)      = show h ++ "<>" ++ show t
  show (Mat n c)      = "λ{[]:" ++ show n ++ ";<>:" ++ show c ++ "}"
  show (Enu s)        = "{" ++ intercalate "," (map (\x -> "@" ++ x) s) ++ "}"
  show (Sym s)        = "@" ++ s
  show (Cse c)        = "λ{" ++ intercalate ";" (map (\(s,t) -> "@" ++ s ++ ":" ++ show t) c) ++ "}"
  show (Sig a b)      = sig a b where
    sig a (Lam "_" f) = show a ++ "&" ++ show (f (Var "_" 0))
    sig a (Lam k f)   = "Σ" ++ k ++ ":" ++ show a ++ "." ++ show (f (Var k 0))
    sig a b           = "Σ" ++ show a ++ "." ++ show b
  show (Tup a b)      = "(" ++ show a ++ "," ++ unwrap (show b) ++ ")"
  show (Get f)        = "λ{(,):" ++ show f ++ "}"
  show (All a b)      = all a b where
    all a (Lam "_" f) = show a ++ "→" ++ show (f (Var "_" 0))
    all a (Lam k f)   = "∀" ++ k ++ ":" ++ show a ++ "." ++ show (f (Var k 0))
    all a b           = "∀" ++ show a ++ "." ++ show b
  show (Lam k f)      = "λ" ++ k ++ "." ++ show (f (Var k 0))
  show (App f x)      = "(" ++ unwrap (show f) ++ " " ++ show x ++ ")"
  show (Eql t a b)    = show t ++ "{" ++ show a ++ "==" ++ show b ++ "}"
  show (Rfl)          = "{==}"
  show (Rwt f)        = "λ{{==}:" ++ show f ++ "}"
  show (Ind t)        = "~{" ++ show t ++ "}"
  show (Frz t)        = "∅" ++ show t
  show (Era)          = "*"
  show (Sup l a b)    = "&" ++ show l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Met _ _ _)    = "?"
  show (Pat s m c)    = "match " ++ unwords (map show s) ++ ":\n" ++ unlines (map clause c) where
    clause (pats,bod) = "  case " ++ unwords (map show pats) ++ " : " ++ show bod

data Error
  = CantInfer Term
  | TypeMismatch Term Term Term
  | TermMismatch Term Term Term

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

instance Show Error where
  show (CantInfer ctx) = 
    "Cant-Infer:" ++
    "\nContext:\n" ++ showContext ctx
  show (TypeMismatch ctx goal typp) = 
    "Type-Mismatch:" ++
    "\n- Goal: " ++ show goal ++ 
    "\n- Type: " ++ show typp ++
    "\nContext:\n" ++ showContext ctx
  show (TermMismatch ctx a b) = 
    "Term-Mismatch:" ++
    "\n- " ++ show a ++ 
    "\n- " ++ show b ++
    "\nContext:\n" ++ showContext ctx

showContext :: Term -> String
showContext ctx = unlines (map snd (reverse (dedup S.empty (reverse (go ctx []))))) where

  isTopFun :: Term -> Bool
  isTopFun t = case t of
    (Fix  _ _)         -> True
    (Chk (Fix _ _) _ ) -> True
    _                  -> False

  go :: Term -> [(Name, String)] -> [(Name, String)]
  go (Let v (Lam k f)) acc
    | isTopFun v = go (f (Var k 0)) acc
    | otherwise  = case v of
        (Chk _ ty) -> go (f (Var k 0)) (acc ++ [(k, "- " ++ k ++ " : " ++ show ty)])
        ty         -> go (f (Var k 0)) (acc ++ [(k, "- " ++ k)])
  go term acc = acc ++ [("", "Term: " ++ show term)]

  dedup :: S.Set Name -> [(Name,String)] -> [(Name,String)]
  dedup _    []                             = []
  dedup seen ((n,l):xs) | n `S.member` seen = dedup seen xs
                        | take 1 n == "_"   = dedup seen xs
                        | otherwise         = (n,l) : dedup (S.insert n seen) xs

-- Utils
-- -----

collectArgs :: Term -> ([(String, Term)], Term)
collectArgs = go [] where
  go acc (All t (Lam k f)) = go (acc ++ [(k, t)]) (f (Var k 0))
  go acc goal              = (acc, goal)

collectApps :: Term -> [Term] -> (Term, [Term])
collectApps (App f x) args = collectApps f (x:args)
collectApps f         args = (f, args)

natToInt :: Term -> Maybe Int
natToInt Zer     = Just 0
natToInt (Suc n) = fmap (+1) (natToInt n)
natToInt _       = Nothing

unwrap :: String -> String
unwrap ('(' : txt) = init txt
unwrap txt         = txt
