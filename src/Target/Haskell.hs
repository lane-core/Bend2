{-./../Core/Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Target.Haskell where

import Core.Type
import Core.WHNF
import Data.List (intercalate)
import qualified Data.Map as M

-- Main compilation function
compile :: Book -> String
compile book@(Book defs _) =
  let compiledFns = map (compileDefn book) (M.toList defs)
  in prelude ++ intercalate "\n\n" compiledFns
  where
    compileDefn :: Book -> (Name, Defn) -> String
    compileDefn book (name, (_, term, typ)) = compileFn book name term typ

-- Prelude necessary for the compiled code to run
prelude :: String
prelude = unlines [
    "{-# LANGUAGE ViewPatterns #-}",
    "import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, complement)",
    "import Data.Char (chr, ord)",
    "import Data.Int (Int64)",
    "import Data.Word (Word64)",
    "import Debug.Trace (trace)",
    "import GHC.Exts (Any)",
    "import Unsafe.Coerce (unsafeCoerce)",
    ""
  ]

-- Compile a function definition
compileFn :: Book -> Name -> Term -> Term -> String
compileFn book name term typ =
  let htm = termToHT book term
      hty = typeToHT book typ
      cleanedName = cleanName name
      args = collectArgs htm
      typeSig = cleanedName ++ " :: " ++ showTerm 0 hty
      fnDef = cleanedName ++ concat (map (\a -> " " ++ a) args) ++ " =\n" ++ indent 2 ++ showTerm 2 (removeArgs (length args) htm)
  in typeSig ++ "\n" ++ fnDef
  where
    collectArgs :: HT -> [String]
    collectArgs (HLam n body) = n : collectArgs body
    collectArgs _ = []
    
    removeArgs :: Int -> HT -> HT
    removeArgs 0 t = t
    removeArgs n (HLam _ body) = removeArgs (n-1) body
    removeArgs _ t = t

-- Compilation from Bend Term to Haskell Term
---------------------------------------------

-- Haskell Term ADT - simplified representation for compilation
data HT
  = HVar Name          -- Variable
  | HRef Name          -- Reference
  | HLam Name HT       -- Lambda abstraction
  | HApp HT HT         -- Function application
  | HLet Name HT HT    -- Let binding
  | HAnn HT HT         -- Annotation
  -- Type constructors
  | HAll HT HT         -- Function type
  | HAny
  | HUni               -- Unit type
  | HBit               -- Bool type
  | HNat               -- Nat type  
  | HLst HT            -- List type
  | HNum NTyp          -- Numeric type
  | HSig HT HT         -- Pair type
  | HEnu               -- Enum type
  -- Data constructors
  | HZer               -- Zero
  | HSuc HT            -- Successor
  | HNil               -- Empty list
  | HCon HT HT         -- List constructor
  | HBt1               -- True
  | HBt0               -- False
  | HOne               -- Unit value
  | HTup HT HT         -- Pair constructor
  | HSym String        -- Symbol
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
  Use k v f   -> termToHT book (f v)
  Set         -> typeToHT book term
  Chk v t     -> HAnn (termToHT book v) (termToHT book t)
  Tst v       -> termToHT book v
  Emp         -> typeToHT book term
  EmpM        -> HLam "x" HEra
  Uni         -> typeToHT book term
  One         -> HOne
  UniM f      -> HLam "_" (termToHT book f)
  Bit         -> typeToHT book term
  Bt0         -> HBt0
  Bt1         -> HBt1
  BitM f t    -> HLam "x" (HMat [HVar "x"] [([HBt0], termToHT book f), ([HBt1], termToHT book t)])
  Nat         -> typeToHT book term
  Zer         -> HZer
  Suc p       -> HSuc (termToHT book p)
  NatM z s    -> HLam "x" (HMat [HVar "x"] [([HZer], termToHT book z), ([HSuc (HVar "n")], HApp (termToHT book s) (HVar "n"))])
  Lst _       -> typeToHT book term
  Nil         -> HNil
  Con h t     -> HCon (termToHT book h) (termToHT book t)
  LstM n c    -> HLam "x" (HMat [HVar "x"] [([HNil], termToHT book n), ([HCon (HVar "h") (HVar "t")], HApp (HApp (termToHT book c) (HVar "h")) (HVar "t"))])
  Enu _       -> HEnu
  Sym s       -> HSym s
  EnuM cs d   -> HLam "x" (HMat [HVar "x"] ((map (\(k,f) -> ([HSym k], termToHT book f)) cs) ++ [([HVar "x"], HApp (termToHT book d) (HVar "x"))]))
  Num _       -> typeToHT book term
  Val v       -> HVal v
  Op2 o a b   -> HOp2 o (termToHT book a) (termToHT book b)
  Op1 o a     -> HOp1 o (termToHT book a)
  Sig _ _     -> typeToHT book term
  Tup a b     -> HTup (termToHT book a) (termToHT book b)
  SigM f      -> HLam "x" (HMat [HVar "x"] [([HTup (HVar "a") (HVar "b")], HApp (HApp (termToHT book f) (HVar "a")) (HVar "b"))])
  All _ _     -> typeToHT book term
  Lam n _ f   -> HLam n (termToHT book (f (Var n 0)))
  -- App (BitM f t) x -> HMat [termToHT book x] [([HBt0], termToHT book f), ([HBt1], termToHT book t)]
  -- App (NatM z s) x -> HMat [termToHT book x] [([HZer], termToHT book z), ([HSuc (HVar "n")], HApp (termToHT book s) (HVar "n"))]
  -- App (LstM n c) x -> HMat [termToHT book x] [([HNil], termToHT book n), ([HCon (HVar "h") (HVar "t")], HApp (HApp (termToHT book c) (HVar "h")) (HVar "t"))]
  -- App (SigM f)   x -> HMat [termToHT book x] [([HTup (HVar "a") (HVar "b")], HApp (HApp (termToHT book f) (HVar "a")) (HVar "b"))]
  App f x     -> HApp (termToHT book f) (termToHT book x)
  Eql _ _ _   -> typeToHT book term
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

-- Convert a type to a Haskell term.
-- Falls back to HAny on types not supported by Haskell (Set, dependent, etc)
typeToHT :: Book -> Type -> HT
typeToHT book t = case whnf book t of
  Var n _     -> HVar n
  Uni         -> HUni
  Bit         -> HBit
  Nat         -> HNat
  Lst t       -> HLst (typeToHT book t)
  Enu ss      -> HEnu
  Num t       -> HNum t
  Sig a b     -> HSig (typeToHT book a) (typeToHT book (whnf book (App b Emp)))
  All a b     -> HAll (typeToHT book a) (typeToHT book (whnf book (App b Emp)))
  Set         -> HAny
  Emp         -> HAny
  Eql t a b   -> HAny
  Era         -> HAny
  _           -> HAny

-- Clean function names for Haskell
cleanName :: String -> String
cleanName = map (\c -> if c == '/' then '\'' else c)

-- Printing of Haskell Terms
----------------------------

indent :: Int -> String
indent i = replicate i ' '

-- Pretty print a Haskell value
showTerm :: Int -> HT -> String
showTerm i term = case term of
  HVar n         -> n
  HRef n         -> cleanName n
  HLam n f       -> "(\\" ++ n ++ " -> " ++ showTerm i f ++ ")"
  HApp f x       -> showApp i term []
  HLet n v f     -> "let " ++ n ++ " = " ++ showTerm (i+7+length n) v ++ " in\n" ++ indent i ++ showTerm i f
  HAnn v t       -> "(" ++ showTerm i v ++ " :: " ++ showTerm i t ++ ")"
  HAll a b       -> showAll i term []
  HAny           -> "Any"
  HUni           -> "()"
  HOne           -> "()"
  HBit           -> "Bool"
  HBt1           -> "True"
  HBt0           -> "False"
  HNat           -> "Integer"
  HZer           -> "(0 :: Integer)"
  HSuc n         -> "(" ++ showTerm i n ++ " + (1 :: Integer))"
  HLst t         -> "[" ++ showTerm i t ++ "]"
  HNil           -> "[]"
  HCon h t       -> "(" ++ showTerm i h ++ " : " ++ showTerm i t ++ ")"
  HSig a b       -> "(" ++ showTerm i a ++ ", " ++ showTerm i b ++ ")"
  HTup a b       -> "(" ++ showTerm i a ++ ", " ++ showTerm i b ++ ")"
  HEnu           -> "String"
  HSym s         -> "\"" ++ s ++ "\""
  HMat xs cs      -> "case " ++ unwords (map (showCoerce i) xs) ++ " of\n" ++ intercalate "\n" (map (showCase (i+2)) cs)
  HNum U64_T     -> "Word64"
  HNum I64_T     -> "Int64"  
  HNum F64_T     -> "Double"
  HNum CHR_T     -> "Char"
  HVal (U64_V n) -> "(" ++ show n ++ " :: Word64)"
  HVal (I64_V n) -> "(" ++ show n ++ " :: Int64)"
  HVal (F64_V n) -> "(" ++ show n ++ " :: Double)"
  HVal (CHR_V c) -> show c
  -- TODO: We need to know the type of the operands and then coerce.
  -- Since op2/op1 are polymorphic with infer on args, we can't coerce directly without annotation.
  HOp2 op a b    -> "(" ++ showCoerce i a ++ " " ++ showOp2 op ++ " (fromIntegral " ++ showCoerce i b ++ "))"
  HOp1 op a      -> "(" ++ showOp1 op ++ " " ++ showCoerce i a ++ ")"
  HLog s x       -> "(trace (" ++ showTerm i s ++ ") (" ++ showTerm i x ++ "))"
  HPri p         -> showPri p
  HEra           -> "undefined"

showCoerce :: Int -> HT -> String
showCoerce i x = "(unsafeCoerce (" ++ showTerm i x ++ "))"

showApp :: Int -> HT -> [HT] -> String
showApp i (HApp f x) acc = showApp i f (x:acc)
showApp i          t acc = "(" ++ unwords (map (showCoerce i) (t:acc)) ++ ")"

showAll :: Int -> HT -> [HT] -> String
showAll i (HAll a b) acc = showAll i b (a:acc)
showAll i          t acc = "(" ++ intercalate " -> " (map (showTerm i) (reverse (t:acc))) ++ ")"

-- Convert case pattern and body to Haskell
showCase :: Int -> ([HT], HT) -> String
showCase i (ps, f) = indent i ++ unwords (map showPat ps) ++ " ->\n" ++ indent (i+2) ++ showCoerce (i+2) f

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
  HSym s   -> "\"" ++ s ++ "\""
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
showPri :: PriF -> String
showPri p = case p of
  U64_TO_CHAR -> "(chr . fromIntegral)"
  CHAR_TO_U64 -> "(fromIntegral . ord)"
  HVM_INC     -> "id"
  HVM_DEC     -> "id"
