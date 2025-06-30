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
whnf :: Book -> Term -> Term
whnf book term
  | ugly nf   = term
  | otherwise = nf
  where nf = whnfGo book term

whnfGo :: Book -> Term -> Term
whnfGo book term =
  case term of
    Let v f    -> whnfLet book v f
    Ref k      -> whnfRef book k
    Fix k f    -> whnfFix book k f
    Ann x _    -> whnf book x
    Chk x _    -> whnf book x
    App f x    -> whnfApp book (App f x) f x
    Loc _ t    -> whnf book t
    Op2 o a b  -> whnfOp2 book o a b
    Op1 o a    -> whnfOp1 book o a
    Pri p      -> Pri p
    UniM x f   -> whnfUniM book term x f
    BitM x f t -> whnfBitM book term x f t
    NatM x z s -> whnfNatM book term x z s
    LstM x n c -> whnfLstM book term x n c
    EnuM x c f -> whnfEnuM book term x c f
    SigM x f   -> whnfSigM book term x f
    EqlM x f   -> whnfEqlM book term x f
    _          -> term

-- Normalizes a let binding
whnfLet :: Book -> Term -> Term -> Term
whnfLet book v f = whnf book (App f v)

-- Normalizes a reference
whnfRef :: Book -> Name -> Term
whnfRef book k =
  case deref book k of
    Just (False, term, _) -> whnf book term
    otherwise             -> Ref k

-- Normalizes a fixpoint
whnfFix :: Book -> String -> Body -> Term
whnfFix book k f = whnf book (f (Fix k f))

-- Normalizes an application
whnfApp :: Book -> Term -> Term -> Term -> Term
whnfApp book undo f x =
  case whnf book f of
    Lam _ f'  -> whnfAppLam book f' x
    Pri p     -> whnfAppPri book undo p x
    Sup _ _ _ -> error "Sup interactions unsupportein Haskell"
    _         -> undo

-- Normalizes a lambda application
whnfAppLam :: Book -> Body -> Term -> Term
whnfAppLam book f x = whnf book (f x)

-- Normalizes a fixpoint application
whnfAppFix :: Book -> Term -> String -> Body -> Term -> Term
whnfAppFix book undo k f x = whnfApp book undo (f (Fix k f)) x

-- Eliminator normalizers
-- ----------------------

-- Normalizes a unit match
whnfUniM :: Book -> Term -> Term -> Term -> Term
whnfUniM book undo x f =
  case whnf book x of
    One -> whnf book f
    _   -> undo

-- Normalizes a boolean match
whnfBitM :: Book -> Term -> Term -> Term -> Term -> Term
whnfBitM book undo x f t =
  case whnf book x of
    Bt0 -> whnf book f
    Bt1 -> whnf book t
    _   -> undo

-- Normalizes a natural number match
whnfNatM :: Book -> Term -> Term -> Term -> Term -> Term
whnfNatM book undo x z s =
  case whnf book x of
    Zer   -> whnf book z
    Suc n -> whnf book (App s (whnf book n))
    _     -> undo

-- Normalizes a list match
whnfLstM :: Book -> Term -> Term -> Term -> Term -> Term
whnfLstM book undo x n c =
  case whnf book x of
    Nil     -> whnf book n
    Con h t -> whnf book (App (App c (whnf book h)) (whnf book t))
    _       -> undo

-- Normalizes a pair match
whnfSigM :: Book -> Term -> Term -> Term -> Term
whnfSigM book undo x f =
  case whnf book x of
    Tup a b -> whnf book (App (App f (whnf book a)) (whnf book b))
    _       -> undo

-- Normalizes an enum match
whnfEnuM :: Book -> Term -> Term -> [(String,Term)] -> Term -> Term
whnfEnuM book undo x c f =
  case whnf book x of
    Sym s -> case lookup s c of
      Just t  -> whnf book t
      Nothing -> whnf book (App f (Sym s))
    _         -> undo

-- Normalizes an equality match
whnfEqlM :: Book -> Term -> Term -> Term -> Term
whnfEqlM book undo x f =
  case whnf book x of
    Rfl -> whnf book f
    _   -> undo

-- Normalizes a primitive application
whnfAppPri :: Book -> Term -> PriF -> Term -> Term
whnfAppPri book undo U64_TO_CHAR x =
  case whnf book x of
    Val (U64_V n) -> Val (CHR_V (toEnum (fromIntegral n)))
    _             -> undo

-- Numeric operations
-- ------------------

whnfOp2 :: Book -> NOp2 -> Term -> Term -> Term
whnfOp2 book op a b =
  case (whnf book a, whnf book b) of
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

whnfOp1 :: Book -> NOp1 -> Term -> Term
whnfOp1 book op a =
  case whnf book a of
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

normal :: Int -> Book -> Term -> Term
normal d book term =
  -- trace ("normal: " ++ show ++ " " ++ show term) $
  case whnf book term of
    Var k i    -> Var k i
    Ref k      -> Ref k
    Sub t      -> normal d book t
    Fix k f    -> Fix k (\x -> normal (d+1) book (f x))
    Let v f    -> Let (normal d book v) (normal d book f)
    Set        -> Set
    Ann x t    -> Ann (normal d book x) (normal d book t)
    Chk x t    -> Chk (normal d book x) (normal d book t)
    Emp        -> Emp
    EmpM x     -> EmpM (normal d book x)
    Uni        -> Uni
    One        -> One
    UniM x f   -> UniM (normal d book x) (normal d book f)
    Bit        -> Bit
    Bt0        -> Bt0
    Bt1        -> Bt1
    BitM x f t -> BitM (normal d book x) (normal d book f) (normal d book t)
    Nat        -> Nat
    Zer        -> Zer
    Suc n      -> Suc (normal d book n)
    NatM x z s -> NatM (normal d book x) (normal d book z) (normal d book s)
    Lst t      -> Lst (normal d book t)
    Nil        -> Nil
    Con h t    -> Con (normal d book h) (normal d book t)
    LstM x n c -> LstM (normal d book x) (normal d book n) (normal d book c)
    Enu s      -> Enu s
    Sym s      -> Sym s
    EnuM x c e -> EnuM (normal d book x) (map (\(s, t) -> (s, normal d book t)) c) (normal d book e)
    Sig a b    -> Sig (normal d book a) (normal d book b)
    Tup a b    -> Tup (normal d book a) (normal d book b)
    SigM x f   -> SigM (normal d book x) (normal d book f)
    All a b    -> All (normal d book a) (normal d book b)
    Lam k f    -> Lam k f -- note: uses lv=0 for finite pretty printing
    App f x    -> foldl (\ f x -> App f (normal d book x)) fn xs
      where (fn,xs) = collectApps (App f x) []
    Eql t a b  -> Eql (normal d book t) (normal d book a) (normal d book b)
    Rfl        -> Rfl
    EqlM x f   -> EqlM (normal d book x) (normal d book f)
    Ind t      -> Ind (normal d book t)
    Frz t      -> Frz (normal d book t)
    Loc l t    -> Loc l (normal d book t)
    Rwt a b x  -> Rwt (normal d book a) (normal d book b) (normal d book x)
    Era        -> Era
    Sup l a b  -> Sup l (normal d book a) (normal d book b)
    Num t      -> Num t
    Val v      -> Val v
    Op2 o a b  -> Op2 o (normal d book a) (normal d book b)
    Op1 o a    -> Op1 o (normal d book a)
    Pri p      -> Pri p
    Met _ _ _  -> error "not-supported"
    Pat _ _ _  -> error "not-supported"

normalCtx :: Int -> Book -> Ctx -> Ctx
normalCtx d book (Ctx ctx) = Ctx (map normalAnn ctx)
  where normalAnn (k,v,t) = (k, normal d book v, normal d book t)

-- Utils
-- =====

-- Forces evaluation
force :: Book -> Term -> Term
force book term =
  case whnf book term of
    Ind t -> force book term
    Frz t -> force book term
    -- term  -> term
    term -> case fn of
      Ref k -> case deref book k of
        Just (_,fn,_) -> force book $ foldl App fn xs
        otherwise     -> term
      otherwise       -> term
      where (fn,xs) = collectApps term []

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
