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
  = ADD | SUB | MUL | DIV | MOD
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
  deriving (Show, Eq)

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
  | Enu [String]             -- {@foo,@bar...}
  | Sym String               -- @foo
  | Cse [(String,Term)] Term -- λ{@foo:f;@bar:b;...d}

  -- Numbers
  | Num NTyp           -- CHR | U64 | I64 | F64
  | Val NVal           -- 123 | +123 | +123.0
  | Op2 NOp2 Term Term -- x + y
  | Op1 NOp1 Term      -- !x

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
  | Loc Span Term

  -- Primitive
  | Pri PriF -- SOME_FUNC

  -- Pattern-Match
  | Pat [Term] [Move] [Case] -- match x ... { with k=v ... ; case @A ...: F ; ... }

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
  show (Var k i)      = k
  show (Ref k)        = k
  -- show (Sub t)        = error "unreachable"
  show (Sub t)        = show t
  show (Fix k f)      = "μ" ++ k ++ ". " ++ show (f (Var k 0))
  show (Let v f)      = "!" ++ show v ++ ";" ++ show f
  show (Set)          = "Set"
  show (Ann x t)      = "<" ++ show x ++ ":" ++ show t ++ ">"
  show (Chk x t)      = "(" ++ show x ++ "::" ++ show t ++ ")"
  show (Emp)          = "Empty"
  show (Efq)          = "λ{}"
  show (Uni)          = "Unit"
  show (One)          = "()"
  show (Use f)        = "λ{ ():" ++ show f ++ " }"
  show (Bit)          = "Bool"
  show (Bt0)          = "False"
  show (Bt1)          = "True"
  show (Bif f t)      = "λ{ False: " ++ show f ++ " ; True: " ++ show t ++ " }"
  show (Nat)          = "Nat"
  show (Zer)          = "0n"
  show (Suc n)        = "1n+" ++ show n
  show (Swi z s)      = "λ{ 0n: " ++ show z ++ " ; 1n+: " ++ show s ++ " }"
  show (Lst t)        = show t ++ "[]"
  show (Nil)          = "[]"
  show (Con h t)      = fromMaybe (show h ++ "<>" ++ show t) (prettyStr (Con h t))
  show (Mat n c)      = "λ{ []:" ++ show n ++ " ; <>:" ++ show c ++ " }"
  show (Enu s)        = "{" ++ intercalate "," (map (\x -> "@" ++ x) s) ++ "}"
  show (Sym s)        = "@" ++ s
  -- show (Cse c)        = "λ{ " ++ intercalate " ; " (map (\(s,t) -> "@" ++ s ++ ": " ++ show t) c) ++ " }"
  show (Cse c e)      = "λ{ " ++ intercalate " ; " (map (\(s,t) -> "@" ++ s ++ ": " ++ show t) c) ++ " ; " ++ show e ++ " }"
  show (Sig a b)      = sig a b where
    sig a (Lam "_" f) = show a ++ "&" ++ show (f (Var "_" 0))
    sig a (Lam k f)   = "Σ" ++ k ++ ":" ++ show a ++ ". " ++ (show (f (Var k 0)))
    sig a b           = "Σ" ++ show a ++ ". " ++ (show b)
  show tup@(Tup _ _)  = fromMaybe ("(" ++ intercalate "," (map show (flattenTup tup)) ++ ")") (prettyCtr tup)
  show (Get f)        = "λ{ (,):" ++ show f ++ " }"
  show (All a b)      = all a b where
    all a (Lam "_" f) = show a ++ " -> " ++ show (f (Var "_" 0))
    all a (Lam k f)   = "∀" ++ k ++ ":" ++ show a ++ ". " ++ (show (f (Var k 0)))
    all a b           = "∀" ++ show a ++ ". " ++ (show b)
  show (Lam k f)      = "λ" ++ k ++ ". " ++ show (f (Var k 0))
  show app@(App _ _)  = fnStr ++ "(" ++ intercalate "," (map show args) ++ ")" where
           (fn, args) = collectApps app []
           fnStr      = case cut fn of
              Var k _ -> k
              Ref k   -> k
              fn      -> "(" ++ show fn ++ ")"
  show (Eql t a b)     = show t ++ "{" ++ show a ++ "==" ++ show b ++ "}"
  show (Rfl)           = "{==}"
  show (Rwt f)         = "λ{ {==}:" ++ show f ++ " }"
  show (Ind t)         = "~{" ++ show t ++ "}"
  show (Frz t)         = "∅" ++ show t
  show (Loc _ t)       = show t
  show (Era)           = "*"
  show (Sup l a b)     = "&" ++ show l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Met _ _ _)     = "?"
  show (Pri p)         = pri p where
    pri U64_TO_CHAR    = "U64_TO_CHAR"
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
  show (Op2 NEQ a b)   = "(" ++ show a ++ " != " ++ show b ++ ")"
  show (Op2 LST a b)   = "(" ++ show a ++ " < " ++ show b ++ ")"
  show (Op2 GRT a b)   = "(" ++ show a ++ " > " ++ show b ++ ")"
  show (Op2 LEQ a b)   = "(" ++ show a ++ " <= " ++ show b ++ ")"
  show (Op2 GEQ a b)   = "(" ++ show a ++ " >= " ++ show b ++ ")"
  show (Op2 AND a b)   = "(" ++ show a ++ " && " ++ show b ++ ")"
  show (Op2 OR a b)    = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Op2 XOR a b)   = "(" ++ show a ++ " ^ " ++ show b ++ ")"
  show (Op2 SHL a b)   = "(" ++ show a ++ " << " ++ show b ++ ")"
  show (Op2 SHR a b)   = "(" ++ show a ++ " >> " ++ show b ++ ")"
  show (Op1 NOT a)     = "(!" ++ show a ++ ")"
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
showContext ctx = 
  let lines = map snd (reverse (dedup S.empty (reverse (go ctx []))))
  in if null lines then "" else init (unlines lines)
  where

  go :: Term -> [(Name, String)] -> [(Name, String)]
  go (Let v (Lam k f)) acc = case v of
    (Chk _ ty) -> go (f (Var k 0)) (acc ++ [(k, "- " ++ k ++ " : " ++ show ty)])
    ty         -> go (f (Var k 0)) (acc ++ [(k, "- " ++ k)])
  go term acc = acc
  -- go term acc = acc ++ [("", "\x1b[1mExpression:\x1b[0m\n- " ++ show term)]

  dedup :: S.Set Name -> [(Name,String)] -> [(Name,String)]
  dedup _    []                             = []
  dedup seen ((n,l):xs) | n `S.member` seen = dedup seen xs
                        | take 1 n == "_"   = dedup seen xs
                        | otherwise         = (n,l) : dedup (S.insert n seen) xs

-- Utils
-- -----

deref :: Book -> Name -> Maybe Defn
deref (Book defs) name = M.lookup name defs

cut :: Term -> Term
cut (Loc _ t) = cut t
cut t         = t

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

noSpan :: Span
noSpan = Span (0,0) (0,0) ""

flattenTup :: Term -> [Term]
flattenTup (Tup l r) = l : flattenTup r
flattenTup t         = [t]

lastElem :: Term -> Maybe Term
lastElem (Tup _ r) = lastElem r
lastElem t         = Just t

prettyCtr :: Term -> Maybe String
prettyCtr (Tup (Sym name) rest) = 
  case lastElem rest of
    Just One -> Just (show (Sym name) ++ "{" ++ intercalate "," (map show (init (flattenTup rest))) ++ "}")
    _        -> Nothing
prettyCtr _ = Nothing

prettyStr :: Term -> Maybe String
prettyStr = go [] where
  go :: [Char] -> Term -> Maybe String
  go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
  go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
  go acc (Loc _ t)                  = go acc t
  go _   _                          = Nothing
