{-./Type.hs-}

module Core.WHNF where

import Debug.Trace

import Core.Type

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

-- Main normalizer
whnf :: Int -> Book -> Term -> Term
whnf lv book term =
  -- trace ("whnf " ++ show term) $
  case term of
    Let v f     -> whnfLet lv book v f
    Ref k       -> whnfRef lv book k
    Fix k f     -> whnfFix lv book k f
    Ann x _     -> whnf lv book x
    Chk x _     -> whnf lv book x
    App f x     -> whnfApp lv book (App f x) f x
    Loc _ t     -> whnf lv book t
    Op2 o a b   -> whnfOp2 lv book o a b
    Op1 o a     -> whnfOp1 lv book o a
    Pri p       -> Pri p
    UniM x f    -> whnfUniM lv book term x f
    BitM x f t  -> whnfBitM lv book term x f t
    NatM x z s  -> whnfNatM lv book term x z s
    LstM x n c  -> whnfLstM lv book term x n c
    EnuM x cs d -> whnfEnuM lv book x cs d
    SigM x f    -> whnfSigM lv book term x f
    EqlM x f    -> whnfEqlM lv book term x f
    _           -> term

-- Normalizes a let binding
whnfLet :: Int -> Book -> Term -> Term -> Term
whnfLet lv book v f = whnf lv book (App f v)

-- Normalizes a reference
whnfRef :: Int -> Book -> Name -> Term
whnfRef lv book k =
  case lv of
    0 -> Ref k
    1 -> case deref book k of
      Just (True , term, _) -> Ref k
      Just (False, term, _) -> whnf lv book term
      Nothing               -> Ref k
    2 -> case deref book k of
      Just (_, term, _) -> whnf lv book term
      Nothing           -> Ref k
    _ -> error "unreachable"

-- Normalizes a fixpoint
whnfFix :: Int -> Book -> String -> Body -> Term
whnfFix lv book k f =
  case lv of
    0 -> Fix k f
    1 -> Fix k f
    2 -> whnf lv book (f (Fix k f))
    _ -> error "unreachable"

-- Normalizes a reference in an application
whnfAppRef :: Int -> Book -> Term -> Name -> Term -> Term
whnfAppRef 0  _    undo k x = App (Ref k) x
whnfAppRef 1  book undo k x =
  case deref book k of
    Just (inj, term, _) | inj       -> App (Ref k) x
                        | otherwise -> whnfApp 1 book undo term x
    Nothing -> App (Ref k) x
whnfAppRef lv book undo k x =
  case deref book k of
    Just (_, term, _) -> whnfApp lv book undo term x
    Nothing           -> undo

-- Normalizes an application
whnfApp :: Int -> Book -> Term -> Term -> Term -> Term
whnfApp lv book undo f x =
  case whnf lv book f of
    Lam _ f'  -> whnfAppLam lv book f' x
    Fix k f'  -> whnfAppFix lv book undo k f' x
    Ref k     -> whnfAppRef lv book undo k x
    Pri p     -> whnfAppPri lv book undo p x
    Sup _ _ _ -> error "Sup interactions unsupported in Haskell"
    _         -> undo

-- Normalizes a lambda application
whnfAppLam :: Int -> Book -> Body -> Term -> Term
whnfAppLam lv book f x = whnf lv book (f x)

-- Normalizes a fixpoint application
whnfAppFix :: Int -> Book -> Term -> String -> Body -> Term -> Term
whnfAppFix 0  book undo k f x = App (Fix k f) x
whnfAppFix lv book undo k f x = whnfApp lv book undo (f (Fix k f)) x

-- Eliminator normalizers
-- ----------------------

-- Normalizes a unit match
whnfUniM :: Int -> Book -> Term -> Term -> Term -> Term
whnfUniM lv book undo x f =
  case whnf lv book x of
    One -> whnf lv book f
    _   -> undo

-- Normalizes a boolean match
whnfBitM :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfBitM lv book undo x f t =
  case whnf lv book x of
    Bt0 -> whnf lv book f
    Bt1 -> whnf lv book t
    _   -> undo

-- Normalizes a natural number match
whnfNatM :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfNatM lv book undo x z s =
  case whnf lv book x of
    Zer   -> whnf lv book z
    Suc n -> whnf lv book (App s (whnf lv book n))
    _     -> undo

-- Normalizes a list match
whnfLstM :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfLstM lv book undo x n c =
  case whnf lv book x of
    Nil     -> whnf lv book n
    Con h t -> whnf lv book (App (App c (whnf lv book h)) (whnf lv book t))
    _       -> undo

-- Normalizes a pair match
whnfSigM :: Int -> Book -> Term -> Term -> Term -> Term
whnfSigM lv book undo x f =
  case whnf lv book x of
    Tup a b -> whnf lv book (App (App f (whnf lv book a)) (whnf lv book b))
    _       -> undo

-- Normalizes an enum match
whnfEnuM :: Int -> Book -> Term -> [(String,Term)] -> Term -> Term
whnfEnuM lv book x cs d =
  case whnf lv book x of
    Sym s -> case lookup s cs of
      Just t  -> whnf lv book t
      Nothing -> whnf lv book (App d (Sym s))
    x'    -> whnf lv book (App d x')

-- Normalizes an equality match
whnfEqlM :: Int -> Book -> Term -> Term -> Term -> Term
whnfEqlM lv book undo x f =
  case whnf lv book x of
    Rfl -> whnf lv book f
    _   -> undo

-- Normalizes a primitive application
whnfAppPri :: Int -> Book -> Term -> PriF -> Term -> Term
whnfAppPri lv book undo U64_TO_CHAR x =
  case whnf lv book x of
    Val (U64_V n) -> Val (CHR_V (toEnum (fromIntegral n)))
    _             -> undo

-- Forces evaluation
force :: Book -> Term -> Term
force book t =
  case whnf 2 book t of
    Ind t -> force book t
    Frz t -> force book t
    t     -> t

-- Numeric operations
-- ------------------

whnfOp2 :: Int -> Book -> NOp2 -> Term -> Term -> Term
whnfOp2 lv book op a b =
  case (whnf lv book a, whnf lv book b) of
    (Val (U64_V x), Val (U64_V y)) -> case op of
      ADD -> Val (U64_V (x + y))
      SUB -> Val (U64_V (x - y))
      MUL -> Val (U64_V (x * y))
      DIV -> if y == 0 then Op2 op (Val (U64_V x)) (Val (U64_V y)) else Val (U64_V (x `div` y))
      MOD -> if y == 0 then Op2 op (Val (U64_V x)) (Val (U64_V y)) else Val (U64_V (x `mod` y))
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      AND -> Val (U64_V (x .&. y))
      OR  -> Val (U64_V (x .|. y))
      XOR -> Val (U64_V (x `xor` y))
      SHL -> Val (U64_V (x `shiftL` fromIntegral y))
      SHR -> Val (U64_V (x `shiftR` fromIntegral y))
    (Val (I64_V x), Val (I64_V y)) -> case op of
      ADD -> Val (I64_V (x + y))
      SUB -> Val (I64_V (x - y))
      MUL -> Val (I64_V (x * y))
      DIV -> if y == 0 then Op2 op (Val (I64_V x)) (Val (I64_V y)) else Val (I64_V (x `div` y))
      MOD -> if y == 0 then Op2 op (Val (I64_V x)) (Val (I64_V y)) else Val (I64_V (x `mod` y))
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      -- Bitwise ops: convert I64 to U64 representation
      AND -> Val (U64_V (fromIntegral x .&. fromIntegral y))
      OR  -> Val (U64_V (fromIntegral x .|. fromIntegral y))
      XOR -> Val (U64_V (fromIntegral x `xor` fromIntegral y))
      SHL -> Val (U64_V (fromIntegral x `shiftL` fromIntegral y))
      SHR -> Val (U64_V (fromIntegral x `shiftR` fromIntegral y))
    (Val (F64_V x), Val (F64_V y)) -> case op of
      ADD -> Val (F64_V (x + y))
      SUB -> Val (F64_V (x - y))
      MUL -> Val (F64_V (x * y))
      DIV -> Val (F64_V (x / y))
      MOD -> Op2 op (Val (F64_V x)) (Val (F64_V y)) -- modulo not defined for floats
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      -- Bitwise ops: convert F64 to U64 bit representation
      AND -> Val (U64_V (castDoubleToWord64 x .&. castDoubleToWord64 y))
      OR  -> Val (U64_V (castDoubleToWord64 x .|. castDoubleToWord64 y))
      XOR -> Val (U64_V (castDoubleToWord64 x `xor` castDoubleToWord64 y))
      SHL -> Val (U64_V (castDoubleToWord64 x `shiftL` fromIntegral (castDoubleToWord64 y)))
      SHR -> Val (U64_V (castDoubleToWord64 x `shiftR` fromIntegral (castDoubleToWord64 y)))
    (Val (CHR_V x), Val (CHR_V y)) -> case op of
      ADD -> Val (CHR_V (toEnum (fromEnum x + fromEnum y)))
      SUB -> Val (CHR_V (toEnum (fromEnum x - fromEnum y)))
      MUL -> Val (CHR_V (toEnum (fromEnum x * fromEnum y)))
      DIV -> if fromEnum y == 0 then Op2 op (Val (CHR_V x)) (Val (CHR_V y)) else Val (CHR_V (toEnum (fromEnum x `div` fromEnum y)))
      MOD -> if fromEnum y == 0 then Op2 op (Val (CHR_V x)) (Val (CHR_V y)) else Val (CHR_V (toEnum (fromEnum x `mod` fromEnum y)))
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      -- Bitwise ops: convert CHR to U64 representation
      AND -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      OR  -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      XOR -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      SHL -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      SHR -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
    (a', b') -> Op2 op a' b'

whnfOp1 :: Int -> Book -> NOp1 -> Term -> Term
whnfOp1 lv book op a =
  case whnf lv book a of
    Val (U64_V x) -> case op of
      NOT -> Val (U64_V (complement x))
      NEG -> Op1 op (Val (U64_V x)) -- negation not defined for unsigned
    Val (I64_V x) -> case op of
      NOT -> Val (U64_V (complement (fromIntegral x))) -- convert to U64 for bitwise
      NEG -> Val (I64_V (-x))
    Val (F64_V x) -> case op of
      NOT -> Val (U64_V (complement (castDoubleToWord64 x))) -- convert to U64 for bitwise
      NEG -> Val (F64_V (-x))
    Val (CHR_V x) -> case op of
      NOT -> Op1 op (Val (CHR_V x)) -- bitwise not defined for chars
      NEG -> Op1 op (Val (CHR_V x)) -- negation not defined for chars
    a' -> Op1 op a'
