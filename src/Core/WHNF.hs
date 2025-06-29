{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.WHNF where

import Debug.Trace

import Core.Type

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

-- Evaluation
-- ==========

-- Levels:
-- - 0: decorations
-- - 1: reduce applications, eliminators, operators and primitives
-- - 2: reduce Fixes and non-injective Refs in wnf position
-- - 3: reduce everything

-- Reduction
whnf :: Int -> Int -> Book -> Term -> Term
whnf lv d book term
  | ugly nf   = term
  | otherwise = nf
  where nf = whnfGo lv d book term

whnfGo :: Int -> Int -> Book -> Term -> Term
whnfGo 0 d book term =
  case term of
    Let v f -> whnfLet 0 d book v f
    Ann x _ -> whnf 0 d book x
    Chk x _ -> whnf 0 d book x
    Loc _ t -> whnf 0 d book t
    _       -> term
whnfGo lv d book term =
  case term of
    Let v f    -> whnfLet lv d book v f
    Ref k      -> whnfRef lv d book k
    Fix k f    -> whnfFix lv d book k f
    Ann x _    -> whnf lv d book x
    Chk x _    -> whnf lv d book x
    App f x    -> whnfApp lv d book (App f x) f x
    Loc _ t    -> whnf lv d book t
    Op2 o a b  -> whnfOp2 lv d book o a b
    Op1 o a    -> whnfOp1 lv d book o a
    Pri p      -> Pri p
    UniM x f   -> whnfUniM lv d book term x f
    BitM x f t -> whnfBitM lv d book term x f t
    NatM x z s -> whnfNatM lv d book term x z s
    LstM x n c -> whnfLstM lv d book term x n c
    EnuM x c f -> whnfEnuM lv d book term x c f
    SigM x f   -> whnfSigM lv d book term x f
    EqlM x f   -> whnfEqlM lv d book term x f
    _          -> term

-- Normalizes a let binding
whnfLet :: Int -> Int -> Book -> Term -> Term -> Term
whnfLet lv d book v f = whnf lv d book (App f v)

-- Normalizes a reference
whnfRef :: Int -> Int -> Book -> Name -> Term
whnfRef lv d book k =
  case lv of
    0 -> Ref k
    1 -> Ref k
    2 -> case deref book k of
      Just (True , term, _) -> Ref k
      Just (False, term, _) -> whnf lv d book term
      Nothing               -> Ref k
    3 -> case deref book k of
      Just (_, term, _) -> whnf lv d book term
      Nothing           -> Ref k
    _ -> error "unreachable"

-- Normalizes a fixpoint
whnfFix :: Int -> Int -> Book -> String -> Body -> Term
whnfFix lv d book k f =
  case lv of
    0 -> Fix k f
    1 -> Fix k f
    2 -> Fix k f
    3 -> whnf lv d book (f (Fix k f))
    _ -> error "unreachable"

-- Normalizes a reference in an application
whnfAppRef :: Int -> Int -> Book -> Term -> Name -> Term -> Term
whnfAppRef 0  d _    undo k x = App (Ref k) x
whnfAppRef 1  d _    undo k x = App (Ref k) x
whnfAppRef 2  d book undo k x =
  case deref book k of
    Just (inj, term, _) | inj       -> App (Ref k) x
                        | otherwise -> whnfApp 1 d book undo term x
    Nothing -> App (Ref k) x
whnfAppRef lv d book undo k x =
  case deref book k of
    Just (_, term, _) -> whnfApp lv d book undo term x
    Nothing           -> undo

-- Normalizes an application
whnfApp :: Int -> Int -> Book -> Term -> Term -> Term -> Term
whnfApp lv d book undo f x =
  case whnf lv d book f of
    Lam _ f'  -> whnfAppLam lv d book f' x
    Fix k f'  -> whnfAppFix lv d book undo k f' x
    Ref k     -> whnfAppRef lv d book undo k x
    Pri p     -> whnfAppPri lv d book undo p x
    Sup _ _ _ -> error "Sup interactions unsupported in Haskell"
    _         -> undo

-- Normalizes a lambda application
whnfAppLam :: Int -> Int -> Book -> Body -> Term -> Term
whnfAppLam lv d book f x = whnf lv d book (f x)

-- Normalizes a fixpoint application
whnfAppFix :: Int -> Int -> Book -> Term -> String -> Body -> Term -> Term
whnfAppFix 0  d book undo k f x = App (Fix k f) x
whnfAppFix 1  d book undo k f x = App (Fix k f) x
whnfAppFix lv d book undo k f x = whnfApp lv d book undo (f (Fix k f)) x

-- Eliminator normalizers
-- ----------------------

-- Normalizes a unit match
whnfUniM :: Int -> Int -> Book -> Term -> Term -> Term -> Term
whnfUniM lv d book undo x f =
  case whnf lv d book x of
    One -> whnf lv d book f
    _   -> undo

-- Normalizes a boolean match
whnfBitM :: Int -> Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfBitM lv d book undo x f t =
  case whnf lv d book x of
    Bt0 -> whnf lv d book f
    Bt1 -> whnf lv d book t
    _   -> undo

-- Normalizes a natural number match
whnfNatM :: Int -> Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfNatM lv d book undo x z s =
  case whnf lv d book x of
    Zer   -> whnf lv d book z
    Suc n -> whnf lv d book (App s (whnf lv d book n))
    _     -> undo

-- Normalizes a list match
whnfLstM :: Int -> Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfLstM lv d book undo x n c =
  case whnf lv d book x of
    Nil     -> whnf lv d book n
    Con h t -> whnf lv d book (App (App c (whnf lv d book h)) (whnf lv d book t))
    _       -> undo

-- Normalizes a pair match
whnfSigM :: Int -> Int -> Book -> Term -> Term -> Term -> Term
whnfSigM lv d book undo x f =
  case whnf lv d book x of
    Tup a b -> whnf lv d book (App (App f (whnf lv d book a)) (whnf lv d book b))
    _       -> undo

-- Normalizes an enum match
whnfEnuM :: Int -> Int -> Book -> Term -> Term -> [(String,Term)] -> Term -> Term
whnfEnuM lv d book undo x c f =
  case whnf lv d book x of
    Sym s -> case lookup s c of
      Just t  -> whnf lv d book t
      Nothing -> whnf lv d book (App f (Sym s))
    _         -> undo

-- Normalizes an equality match
whnfEqlM :: Int -> Int -> Book -> Term -> Term -> Term -> Term
whnfEqlM lv d book undo x f =
  case whnf lv d book x of
    Rfl -> whnf lv d book f
    _   -> undo

-- Normalizes a primitive application
whnfAppPri :: Int -> Int -> Book -> Term -> PriF -> Term -> Term
whnfAppPri lv d book undo U64_TO_CHAR x =
  case whnf lv d book x of
    Val (U64_V n) -> Val (CHR_V (toEnum (fromIntegral n)))
    _             -> undo

-- Numeric operations
-- ------------------

whnfOp2 :: Int -> Int -> Book -> NOp2 -> Term -> Term -> Term
whnfOp2 lv d book op a b =
  case (whnf lv d book a, whnf lv d book b) of
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
      POW -> Val (U64_V (x ^ y))
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
      POW -> Val (I64_V (x ^ y))
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
      POW -> Val (F64_V (x ** y))
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
      POW -> Val (CHR_V (toEnum ((fromEnum x) ^ (fromEnum y))))
    (a', b') -> Op2 op a' b'

whnfOp1 :: Int -> Int -> Book -> NOp1 -> Term -> Term
whnfOp1 lv d book op a =
  case whnf lv d book a of
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

-- Normalization
-- =============

normal :: Int -> Int -> Book -> Term -> Term
normal lv d book term =
  -- trace ("normal: " ++ show lv ++ " " ++ show term) $
  case whnf lv d book term of
    Var k i    -> Var k i
    Ref k      -> Ref k
    Sub t      -> normal lv d book t
    Fix k f    -> Fix k (\x -> normal lv (d+1) book (f x))
    Let v f    -> Let (normal lv d book v) (normal lv d book f)
    Set        -> Set
    Ann x t    -> Ann (normal lv d book x) (normal lv d book t)
    Chk x t    -> Chk (normal lv d book x) (normal lv d book t)
    Emp        -> Emp
    EmpM x     -> EmpM (normal lv d book x)
    Uni        -> Uni
    One        -> One
    UniM x f   -> UniM (normal lv d book x) (normal lv d book f)
    Bit        -> Bit
    Bt0        -> Bt0
    Bt1        -> Bt1
    BitM x f t -> BitM (normal lv d book x) (normal lv d book f) (normal lv d book t)
    Nat        -> Nat
    Zer        -> Zer
    Suc n      -> Suc (normal lv d book n)
    NatM x z s -> NatM (normal lv d book x) (normal lv d book z) (normal lv d book s)
    Lst t      -> Lst (normal lv d book t)
    Nil        -> Nil
    Con h t    -> Con (normal lv d book h) (normal lv d book t)
    LstM x n c -> LstM (normal lv d book x) (normal lv d book n) (normal lv d book c)
    Enu s      -> Enu s
    Sym s      -> Sym s
    EnuM x c e -> EnuM (normal lv d book x) (map (\(s, t) -> (s, normal lv d book t)) c) (normal lv d book e)
    Sig a b    -> Sig (normal lv d book a) (normal lv d book b)
    Tup a b    -> Tup (normal lv d book a) (normal lv d book b)
    SigM x f   -> SigM (normal lv d book x) (normal lv d book f)
    All a b    -> All (normal lv d book a) (normal lv d book b)
    Lam k f    -> Lam k (\x -> normal 0 (d+1) book (f x)) -- note: uses lv=0 for finite pretty printing
    App f x    -> App (normal 1  d book f) (normal lv d book x)
    Eql t a b  -> Eql (normal lv d book t) (normal lv d book a) (normal lv d book b)
    Rfl        -> Rfl
    EqlM x f   -> EqlM (normal lv d book x) (normal lv d book f)
    Ind t      -> Ind (normal lv d book t)
    Frz t      -> Frz (normal lv d book t)
    Loc l t    -> Loc l (normal lv d book t)
    Rwt a b x  -> Rwt (normal lv d book a) (normal lv d book b) (normal lv d book x)
    Era        -> Era
    Sup l a b  -> Sup l (normal lv d book a) (normal lv d book b)
    Num t      -> Num t
    Val v      -> Val v
    Op2 o a b  -> Op2 o (normal lv d book a) (normal lv d book b)
    Op1 o a    -> Op1 o (normal lv d book a)
    Pri p      -> Pri p
    Met _ _ _  -> error "not-supported"
    Pat _ _ _  -> error "not-supported"

normalCtx :: Int -> Int -> Book -> Ctx -> Ctx
normalCtx lv d book (Ctx ctx) = Ctx (map normalAnn ctx)
  where normalAnn (k,v,t) = (k, normal lv d book v, normal lv d book t)

-- Utils
-- =====

-- Forces evaluation
force :: Int -> Book -> Term -> Term
force d book t =
  case whnf 3 d book t of
    Ind t -> force d book t
    Frz t -> force d book t
    t     -> t

-- Shapes that are rolled back for pretty printing
-- These shapes are stuck, so, this shouldn't affect proving
ugly :: Term -> Bool
ugly (cut -> UniM _ _  ) = True
ugly (cut -> BitM _ _ _) = True
ugly (cut -> NatM _ _ _) = True
ugly (cut -> LstM _ _ _) = True
ugly (cut -> EnuM _ _ _) = True
ugly (cut -> SigM _ _  ) = True
ugly (cut -> EqlM _ _  ) = True
ugly _                   = False
