{-./Type.hs-}

module Core.WHNF where

import Debug.Trace

import Core.Type

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

whnf :: Int -> Book -> Term -> Term
whnf lv book term = do
  -- trace ("whnf " ++ show term) $
  case term of
    Let v f   -> whnfLet lv book v f
    Ref k     -> whnfRef lv book k
    Fix k f   -> whnfFix lv book k f
    Ann x _   -> whnf lv book x
    Chk x _   -> whnf lv book x
    App f x   -> whnfApp lv book (App f x) f x
    Loc _ t   -> whnf lv book t
    Op2 o a b -> whnfOp2 lv book o a b
    Op1 o a   -> whnfOp1 lv book o a
    Pri p     -> Pri p
    _         -> term

whnfLet :: Int -> Book -> Term -> Term -> Term
whnfLet lv book v f = whnf lv book (App f v)

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

whnfFix :: Int -> Book -> String -> Body -> Term
whnfFix lv book k f =
  case lv of
    0 -> Fix k f
    1 -> Fix k f
    2 -> whnf lv book (f (Fix k f))
    _ -> error "unreachable"

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

whnfApp :: Int -> Book -> Term -> Term -> Term -> Term
whnfApp lv book undo f x = 
  case app (whnf lv book f) x of
    App (Bif _ _) x -> undo
    App (Swi _ _) x -> undo
    App (Mat _ _) x -> undo
    App (Cse _ _) x -> undo
    App (Use _  ) x -> undo
    App (Get _  ) x -> undo
    App (Rwt _  ) x -> undo
    res             -> res
  where
    app (Lam _ f  ) x = whnfAppLam lv book f x
    app (Sup l a b) x = error "not-supported"
    app (Fix k f  ) x = whnfAppFix lv book undo k f x
    app (Ref k    ) x = whnfAppRef lv book undo k x
    app (Use f    ) x = whnfAppUse lv book undo f x
    app (Bif f t  ) x = whnfAppBif lv book undo f t x
    app (Swi z s  ) x = whnfAppSwi lv book undo z s x
    app (Mat n c  ) x = whnfAppMat lv book undo n c x
    app (Cse c e  ) x = whnfAppCse lv book undo c e x
    app (Get f    ) x = whnfAppGet lv book undo f x
    app (Pri p    ) x = whnfAppPri lv book undo p x
    app _           x = undo

whnfAppLam :: Int -> Book -> Body -> Term -> Term
whnfAppLam lv book f x = whnf lv book (f x)

whnfAppFix :: Int -> Book -> Term -> String -> Body -> Term -> Term
whnfAppFix 0  book undo k f x = App (Fix k f) x
whnfAppFix lv book undo k f x = whnfApp lv book undo (f (Fix k f)) x

whnfAppUse :: Int -> Book -> Term -> Term -> Term -> Term
whnfAppUse lv book undo f x =
  case whnf lv book x of
    One -> whnf lv book f
    _   -> undo

whnfAppBif :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfAppBif lv book undo t0 t1 x =
  case whnf lv book x of
    Bt0 -> whnf lv book t0
    Bt1 -> whnf lv book t1
    _   -> undo

whnfAppSwi :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfAppSwi lv book undo z s x =
  case whnf lv book x of
    Zer       -> whnf lv book z
    Suc n     -> whnf lv book (App s (whnf lv book n))
    Sup l a b -> error "Sup interactions unsupported in Haskell"
    _         -> undo

whnfAppMat :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfAppMat lv book undo n c x =
  case whnf lv book x of
    Nil       -> whnf lv book n
    Con h t   -> whnf lv book (App (App c (whnf lv book h)) (whnf lv book t))
    Sup l a b -> error "Sup interactions unsupported in Haskell"
    _         -> undo

whnfAppGet :: Int -> Book -> Term -> Term -> Term -> Term
whnfAppGet lv book undo f x =
  case whnf lv book x of
    Tup a b -> whnf lv book (App (App f (whnf lv book a)) (whnf lv book b))
    _       -> undo

whnfAppCse :: Int -> Book -> Term -> [(String,Term)] -> Term -> Term -> Term
whnfAppCse lv book undo c d x =
  case whnf lv book x of
    Sym s -> case lookup s c of
      Just t  -> whnf lv book t
      Nothing -> whnf lv book (App d (Sym s))
    _     -> undo

whnfAppPri :: Int -> Book -> Term -> PriF -> Term -> Term
whnfAppPri lv book undo U64_TO_CHAR x =
  case whnf lv book x of
    Val (U64_V n) -> Val (CHR_V (toEnum (fromIntegral n)))
    _             -> undo

force :: Book -> Term -> Term
force book t =
  case whnf 2 book t of
    Ind t -> force book t
    Frz t -> force book t
    t     -> t

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
