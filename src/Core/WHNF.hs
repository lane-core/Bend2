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

data EvalLevel
  = Soft
  | Full
  deriving (Show,Eq)

-- Levels:
-- - 0: undo ugly forms
-- - 1: full evaluation

-- Reduction
whnf :: EvalLevel -> Book -> Term -> Term
whnf lv book term
  | lv == Soft && ugly nf = term
  | otherwise             = nf
  where nf = whnfGo lv book term

whnfGo :: EvalLevel -> Book -> Term -> Term
whnfGo lv book term =
  case term of
    Let v f    -> whnfLet lv book v f
    Ref k      -> whnfRef lv book k
    Fix k f    -> whnfFix lv book k f
    Chk x _    -> whnf lv book x
    App f x    -> whnfApp lv book f x
    Loc _ t    -> whnf lv book t
    Op2 o a b  -> whnfOp2 lv book o a b
    Op1 o a    -> whnfOp1 lv book o a
    Pri p      -> Pri p
    UniM x f   -> whnfUniM lv book x f
    BitM x f t -> whnfBitM lv book x f t
    NatM x z s -> whnfNatM lv book x z s
    LstM x n c -> whnfLstM lv book x n c
    EnuM x c f -> whnfEnuM lv book x c f
    SigM x f   -> whnfSigM lv book x f
    EqlM x f   -> whnfEqlM lv book x f
    Log s x    -> whnfLog lv book s x
    _          -> term

-- Normalizes a let binding
whnfLet :: EvalLevel -> Book -> Term -> Term -> Term
whnfLet lv book v f = whnf lv book (App f v)

-- Normalizes a reference
whnfRef :: EvalLevel -> Book -> Name -> Term
whnfRef lv book k =
  case deref book k of
    Just (False, term, _) -> whnf lv book term
    otherwise             -> Ref k

-- Normalizes a fixpoint
whnfFix :: EvalLevel -> Book -> String -> Body -> Term
whnfFix lv book k f = whnf lv book (f (Fix k f))

-- Normalizes an application
whnfApp :: EvalLevel -> Book -> Term -> Term -> Term
whnfApp lv book f x =
  case whnf lv book f of
    Lam _ f'  -> whnfAppLam lv book f' x
    Pri p     -> whnfAppPri lv book p x
    Sup _ _ _ -> error "Sup interactions unsupported in Haskell"
    Frk _ _ _ -> error "Fork interactions unsupported in Haskell"
    _         -> App f x

-- Normalizes a lambda application
whnfAppLam :: EvalLevel -> Book -> Body -> Term -> Term
whnfAppLam lv book f x = whnf lv book (f x)

-- Normalizes a fixpoint application
whnfAppFix :: EvalLevel -> Book -> String -> Body -> Term -> Term
whnfAppFix lv book k f x = whnfApp lv book (f (Fix k f)) x

-- Eliminator normalizers
-- ----------------------

-- Normalizes a unit match
whnfUniM :: EvalLevel -> Book -> Term -> Term -> Term
whnfUniM lv book x f =
  case whnf lv book x of
    One -> whnf lv book f
    _   -> UniM x f

-- Normalizes a boolean match
whnfBitM :: EvalLevel -> Book -> Term -> Term -> Term -> Term
whnfBitM lv book x f t =
  case whnf lv book x of
    Bt0 -> whnf lv book f
    Bt1 -> whnf lv book t
    _   -> BitM x f t

-- Normalizes a natural number match
whnfNatM :: EvalLevel -> Book -> Term -> Term -> Term -> Term
whnfNatM lv book x z s =
  case whnf lv book x of
    Zer   -> whnf lv book z
    Suc n -> whnf lv book (App s (whnf lv book n))
    _     -> NatM x z s

-- Normalizes a list match
whnfLstM :: EvalLevel -> Book -> Term -> Term -> Term -> Term
whnfLstM lv book x n c =
  case whnf lv book x of
    Nil     -> whnf lv book n
    Con h t -> whnf lv book (App (App c (whnf lv book h)) (whnf lv book t))
    _       -> LstM x n c

-- Normalizes a pair match
whnfSigM :: EvalLevel -> Book -> Term -> Term -> Term
whnfSigM lv book x f =
  case whnf lv book x of
    Tup a b -> whnf lv book (App (App f (whnf lv book a)) (whnf lv book b))
    _       -> SigM x f

-- Normalizes an enum match
whnfEnuM :: EvalLevel -> Book -> Term -> [(String,Term)] -> Term -> Term
whnfEnuM lv book x c f =
  case whnf lv book x of
    Sym s -> case lookup s c of
      Just t  -> whnf lv book t
      Nothing -> whnf lv book (App f (Sym s))
    _         -> EnuM x c f

-- Normalizes an equality match
whnfEqlM :: EvalLevel -> Book -> Term -> Term -> Term
whnfEqlM lv book x f =
  case whnf lv book x of
    Rfl -> whnf lv book f
    _   -> EqlM x f

-- Normalizes a log operation
whnfLog :: EvalLevel -> Book -> Term -> Term -> Term
whnfLog lv book s x =
  let extractString :: Term -> Maybe String
      extractString Nil = Just ""
      extractString (Con (Val (CHR_V c)) rest) = do
        restStr <- extractString (whnf lv book rest)
        return (c : restStr)
      extractString (Loc _ t) = extractString t
      extractString _ = Nothing
  in case extractString (whnf lv book s) of
       Just str -> trace str (whnf lv book x)
       Nothing  -> whnf lv book x

-- Normalizes a primitive application
whnfAppPri :: EvalLevel -> Book -> PriF -> Term -> Term
whnfAppPri lv book U64_TO_CHAR x =
  case whnf lv book x of
    Val (U64_V n) -> Val (CHR_V (toEnum (fromIntegral n)))
    _             -> App (Pri U64_TO_CHAR) x

-- Numeric operations
-- ------------------

whnfOp2 :: EvalLevel -> Book -> NOp2 -> Term -> Term -> Term
whnfOp2 lv book op a b =
  case (whnf lv book a, whnf lv book b) of
    -- Bool operations
    (Bt0, Bt0) -> case op of
      AND -> Bt0
      OR  -> Bt0
      XOR -> Bt0
      EQL -> Bt1
      NEQ -> Bt0
      _   -> Op2 op Bt0 Bt0
    (Bt0, Bt1) -> case op of
      AND -> Bt0
      OR  -> Bt1
      XOR -> Bt1
      EQL -> Bt0
      NEQ -> Bt1
      _   -> Op2 op Bt0 Bt1
    (Bt1, Bt0) -> case op of
      AND -> Bt0
      OR  -> Bt1
      XOR -> Bt1
      EQL -> Bt0
      NEQ -> Bt1
      _   -> Op2 op Bt1 Bt0
    (Bt1, Bt1) -> case op of
      AND -> Bt1
      OR  -> Bt1
      XOR -> Bt0
      EQL -> Bt1
      NEQ -> Bt0
      _   -> Op2 op Bt1 Bt1
    -- Numeric operations
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

whnfOp1 :: EvalLevel -> Book -> NOp1 -> Term -> Term
whnfOp1 lv book op a =
  case whnf lv book a of
    -- Bool operations
    Bt0 -> case op of
      NOT -> Bt1
      _   -> Op1 op Bt0
    Bt1 -> case op of
      NOT -> Bt0
      _   -> Op1 op Bt1
    -- Numeric operations
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
  case whnf Soft book term of
    Var k i    -> Var k i
    Ref k      -> Ref k
    Sub t      -> t
    Fix k f    -> Fix k (\x -> normal (d+1) book (f (Sub x)))
    Let v f    -> Let (normal d book v) (normal d book f)
    Set        -> Set
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
    Lam k f    -> Lam k (\x -> normal d book (f (Sub x)))
    App f x    -> foldl (\ f x -> App f (normal d book x)) fn xs
      where (fn,xs) = collectApps (App f x) []
    Eql t a b  -> Eql (normal d book t) (normal d book a) (normal d book b)
    Rfl        -> Rfl
    EqlM x f   -> EqlM (normal d book x) (normal d book f)
    Ind t      -> Ind (normal d book t)
    Frz t      -> Frz (normal d book t)
    Loc l t    -> Loc l (normal d book t)
    Rwt a b x  -> Rwt (normal d book a) (normal d book b) (normal d book x)
    Log s x    -> Log (normal d book s) (normal d book x)
    Era        -> Era
    Sup l a b  -> Sup l (normal d book a) (normal d book b)
    Frk l a b  -> error "Fork interactions unsupported in Haskell"
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

-- Shapes that are rolled back for pretty printing
-- This is safe because these terms are stuck
ugly :: Term -> Bool
ugly (cut -> UniM _ _  ) = True
ugly (cut -> BitM _ _ _) = True
ugly (cut -> NatM _ _ _) = True
ugly (cut -> LstM _ _ _) = True
ugly (cut -> EnuM _ _ _) = True
ugly (cut -> SigM _ _  ) = True
ugly (cut -> EqlM _ _  ) = True
ugly _                   = False

-- Evaluates terms that whnf won't, including:
-- - Type decorations like Ind/Frz
-- - Injective Refs (whnf skips them for pretty printing)
force :: Book -> Term -> Term
force book term =
  case whnf Full book term of
    Ind t -> force book term
    Frz t -> force book term
    term  -> case fn of
      Ref k -> case deref book k of
        Just (_,fn,_) -> force book $ foldl App fn xs
        otherwise     -> term
      otherwise       -> term
      where (fn,xs) = collectApps term []
