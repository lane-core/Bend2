{-./../Core/Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Target.Haskell where

import Core.Type
import Data.List (intercalate)
import qualified Data.Map as M

-- Haskell Term ADT - simplified representation for compilation
data HT
  = HVar Name          -- Variable
  | HRef Name          -- Reference
  | HLam Name HT       -- Lambda abstraction
  | HApp HT HT         -- Function application
  | HLet Name HT HT    -- Let binding
  -- Type constructors
  | HBit               -- Bool type
  | HNat               -- Nat type  
  | HLst HT            -- List type
  | HNum NTyp          -- Numeric type
  | HSig HT HT         -- Pair type
  | HAll HT HT         -- Function type
  | HUni               -- Unit type
  -- Data constructors
  | HZer               -- Zero
  | HSuc HT            -- Successor
  | HNil               -- Empty list
  | HCon HT HT         -- List constructor
  | HBt1               -- True
  | HBt0               -- False
  | HOne               -- Unit value
  | HTup HT HT         -- Pair constructor
  -- Pattern matching
  | HMat [HT] [([HT], HT)] -- Case expression with Term patterns
  -- Numeric values
  | HVal NVal          -- Numeric literals
  | HOp2 NOp2 HT HT    -- Binary operations
  | HOp1 NOp1 HT       -- Unary operations
  -- Other
  | HPri PriF          -- Primitives
  | HLog HT HT         -- Log expression
  | HEra

-- Convert Bend Term to Haskell Term
termToHT :: Book -> Term -> HT
termToHT book term = case term of
  Var n _     -> HVar n
  Ref k _     -> HRef k -- TODO: remove erased args from the reference
  Sub t       -> termToHT book t
  Fix n f     -> HLet n (termToHT book (f (Var n 0))) (HVar n)
  Let k _ v f -> HLet k (termToHT book v) (termToHT book (f (Var k 0))) -- TODO: deal with repeated bind names (lets are recursive in HS)
  Use k v f   -> termToHT book (f v)  -- Inline directly
  Set         -> HUni
  Chk v _     -> termToHT book v
  Tst v       -> termToHT book v
  Emp         -> HEra
  EmpM        -> HLam "x" HEra
  Uni         -> HUni
  One         -> HOne
  UniM f      -> HLam "_" (termToHT book f)
  Bit         -> HBit
  Bt0         -> HBt0
  Bt1         -> HBt1
  BitM f t    -> HLam "x" (HMat [HVar "x"] [([HBt0], termToHT book f), ([HBt1], termToHT book t)])
  Nat         -> HNat
  Zer         -> HZer
  Suc p       -> HSuc (termToHT book p)
  NatM z s    -> HLam "x" (HMat [HVar "x"] [([HZer], termToHT book z), ([HSuc (HVar "n")], HApp (termToHT book s) (HVar "n"))])
  Lst t       -> HLst (termToHT book t)
  Nil         -> HNil
  Con h t     -> HCon (termToHT book h) (termToHT book t)
  LstM n c    -> HLam "x" (HMat [HVar "x"] [([HNil], termToHT book n), ([HCon (HVar "h") (HVar "t")], HApp (HApp (termToHT book c) (HVar "h")) (HVar "t"))])
  Enu ss      -> HEra
  Sym s       -> error "Raw symbols not supported for Haskell compilation"
  EnuM cs d   -> error "Raw enum matches not supported for Haskell compilation"
  Num t       -> HNum t
  Val v       -> HVal v
  Op2 o a b   -> HOp2 o (termToHT book a) (termToHT book b)
  Op1 o a     -> HOp1 o (termToHT book a)
  Sig a b     -> -- TODO: Constructor types
    case b of
      Lam _ _ b -> HSig (termToHT book a) (termToHT book (b (Var "_" 0)))
      _         -> error "Sigma with pattern-matching bind not supported for Haskell compilation"
  Tup a b     -> HTup (termToHT book a) (termToHT book b)
  SigM f      -> HLam "x" (HMat [HVar "x"] [([HTup (HVar "a") (HVar "b")], HApp (HApp (termToHT book f) (HVar "a")) (HVar "b"))])
  All a b     ->
    case b of
      Lam _ _ b -> HAll (termToHT book a) (termToHT book (b (Var "_" 0)))
      _         -> error "Forall with pattern-matching bind not supported for Haskell compilation"
  Lam n _ f   -> HLam n (termToHT book (f (Var n 0)))
  App (BitM f t) x -> HMat [termToHT book x] [([HBt0], termToHT book f), ([HBt1], termToHT book t)]
  App (NatM z s) x -> HMat [termToHT book x] [([HZer], termToHT book z), ([HSuc (HVar "n")], HApp (termToHT book s) (HVar "n"))]
  App (LstM n c) x -> HMat [termToHT book x] [([HNil], termToHT book n), ([HCon (HVar "h") (HVar "t")], HApp (HApp (termToHT book c) (HVar "h")) (HVar "t"))]
  App (SigM f)   x -> HMat [termToHT book x] [([HTup (HVar "a") (HVar "b")], HApp (HApp (termToHT book f) (HVar "a")) (HVar "b"))]
  App f x     -> HApp (termToHT book f) (termToHT book x)
  Eql t a b   -> HEra
  Rfl         -> HEra
  EqlM f      -> HLam "_" (termToHT book f)
  Rwt _ f     -> termToHT book f
  Met _ _ _   -> error "Metas not supported for Haskell compilation"
  Era         -> HEra
  Sup _ _ _   -> error "Superpositions not supported for Haskell compilation"
  SupM _ _    -> error "Superposition matches not supported for Haskell compilation"
  Log s x     -> HLog (termToHT book s) (termToHT book x)
  Loc _ t     -> termToHT book t
  Pri p       -> HPri p
  Pat xs _ cs -> HMat (map (termToHT book) xs) (map (\(ps, b) -> (map (termToHT book) ps, termToHT book b)) cs)
  Frk _ _ _   -> error "Fork not supported for Haskell compilation"

-- Printing of Haskell Term
---------------------------

indent :: Int -> String
indent i = replicate i ' '

-- Pretty print Haskell Term to Haskell code
showHT :: Int -> HT -> String
showHT i term = case term of
  HVar n         -> n
  HRef n         -> cleanName n
  HLam n f       -> "(\\" ++ n ++ " -> " ++ showHT i f ++ ")"
  HApp f x       -> showApp i f [x]
  HLet n v f     -> "let " ++ n ++ " = " ++ showHT (i+7+length n) v ++ " in\n" ++ indent i ++ showHT i f
  HBit           -> "Bool"
  HNat           -> "Integer"
  HLst t         -> "[" ++ showHT i t ++ "]"
  HNum U64_T     -> "Word64"
  HNum I64_T     -> "Int64"  
  HNum F64_T     -> "Double"
  HNum CHR_T     -> "Char"
  HSig a b       -> "(" ++ showHT i a ++ ", " ++ showHT i b ++ ")"
  HAll a b       -> showAll i b [a]
  HZer           -> "0"
  HSuc n         -> "(" ++ showHT i n ++ " + 1)"
  HNil           -> "[]"
  HCon h t       -> "(" ++ showHT i h ++ " : " ++ showHT i t ++ ")"
  HBt1           -> "True"
  HBt0           -> "False"
  HUni           -> "()"
  HOne           -> "()"
  HTup a b       -> "(" ++ showHT i a ++ ", " ++ showHT i b ++ ")"
  HMat xs cs      -> "case " ++ unwords (map (showHT i) xs) ++ " of\n" ++ intercalate "\n" (map (showCase (i+2)) cs)
  HVal (U64_V n) -> show n
  HVal (I64_V n) -> show n
  HVal (F64_V n) -> show n
  HVal (CHR_V c) -> show c
  HOp2 op a b    -> "(" ++ showHT i a ++ " " ++ showOp2 op ++ " (fromIntegral " ++ showHT i b ++ "))"
  HOp1 op a      -> "(" ++ showOp1 op ++ " " ++ showHT i a ++ ")"
  HEra           -> "undefined"
  HLog s x       -> "(trace (" ++ showHT i s ++ ") (" ++ showHT i x ++ "))"
  HPri p         -> priToHaskell p

showApp :: Int -> HT -> [HT] -> String
showApp i (HApp f x) acc = showApp i f (x:acc)
showApp i          t acc = "(" ++ unwords (map (showHT i) (t:acc)) ++ ")"

showAll :: Int -> HT -> [HT] -> String
showAll i (HAll a b) acc = showAll i b (a:acc)
showAll i          t acc = "(" ++ intercalate " -> " (map (showHT i) (reverse (t:acc))) ++ ")"

-- Convert case pattern and body to Haskell
showCase :: Int -> ([HT], HT) -> String
showCase i (ps, f) = indent i ++ unwords (map showPat ps) ++ " ->\n" ++ indent (i+2) ++ showHT (i+2) f

showPat :: HT -> String
showPat pat = case pat of
  HVar n   -> n
  HTup a b -> "(" ++ showPat a ++ ", " ++ showPat b ++ ")"
  HCon h t -> "(" ++ showPat h ++ " : " ++ showPat t ++ ")"
  HNil     -> "[]"
  HZer     -> "0"
  HSuc n   -> "(pred -> " ++ showPat n ++ ")"
  HBt1     -> "True"
  HBt0     -> "False"
  _ -> error "Invalid pattern"

-- Convert binary operators to Haskell
showOp2 :: NOp2 -> String
showOp2 op = case op of
  ADD -> "+"
  SUB -> "-"
  MUL -> "*"
  DIV -> "`div`"
  MOD -> "`mod`"
  POW -> "^"
  EQL -> "=="
  NEQ -> "/="
  LST -> "<"
  GRT -> ">"
  LEQ -> "<="
  GEQ -> ">="
  AND -> ".&."  -- Bitwise operations
  OR  -> ".|."
  XOR -> "`xor`"
  SHL -> "`shiftL`"
  SHR -> "`shiftR`"

-- Convert unary operators to Haskell
showOp1 :: NOp1 -> String
showOp1 op = case op of
  NOT -> "complement"
  NEG -> "negate"

-- Convert primitives to Haskell
priToHaskell :: PriF -> String
priToHaskell p = case p of
  U64_TO_CHAR -> "(chr . fromIntegral)"
  CHAR_TO_U64 -> "(fromIntegral . ord)"
  HVM_INC     -> "id"
  HVM_DEC     -> "id"

-- Clean function names for Haskell
cleanName :: String -> String
cleanName = map (\c -> if c == '/' then '\'' else c)

-- Compile a function definition
compileFn :: Book -> Name -> Term -> Term -> String
compileFn book name term typ =
  let htm = termToHT book term
      hty = termToHT book typ
      cleanedName = cleanName name
      args = collectArgs htm
      typeSig = cleanedName ++ " :: " ++ showHT 0 hty
      fnDef = cleanedName ++ concat (map (\a -> " " ++ a) args) ++ " =\n" ++ indent 2 ++ showHT 2 (removeArgs (length args) htm)
  in typeSig ++ "\n" ++ fnDef
  where
    collectArgs :: HT -> [String]
    collectArgs (HLam n body) = n : collectArgs body
    collectArgs _ = []
    
    removeArgs :: Int -> HT -> HT
    removeArgs 0 t = t
    removeArgs n (HLam _ body) = removeArgs (n-1) body
    removeArgs _ t = t

-- Generate Haskell prelude
prelude :: String
prelude = unlines [
    "{-# LANGUAGE ViewPatterns #-}",
    "import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, complement)",
    "import Data.Char (chr, ord)",
    "import Debug.Trace (trace)",
    "import Data.Word (Word64)",
    "import Data.Int (Int64)",
    ""
  ]

-- Main compilation function
compile :: Book -> String
compile book@(Book defs _) =
  let compiledFns = map (compileDefn book) (M.toList defs)
  in prelude ++ intercalate "\n\n" compiledFns
  where
    compileDefn :: Book -> (Name, Defn) -> String
    compileDefn book (name, (_, term, typ)) = compileFn book name term typ