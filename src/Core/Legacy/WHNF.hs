{-./Type.hs-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
-- {-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Legacy.WHNF where

import Data.Bifunctor
import Data.Bits
import Data.IORef
import Data.Kind
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import System.IO.Unsafe

import Debug.Trace

import Core.Sort

-- Evaluation
-- ==========

-- Reduction
whnf :: Book -> Expr -> Expr
whnf =
  -- trace ("whnf: " ++ show term) $
  whnfGo

whnfGo :: Book -> Expr -> Expr
whnfGo book term =
  case term of
    Let k t v f -> whnfLet book v f
    Use k v f -> whnfUse book v f
    Ref k i -> whnfRef book k i
    Fix k f -> whnfFix book k f
    Chk x _ -> whnf book x
    Tst x -> whnf book x
    App f x -> whnfApp book f x
    Loc _ t -> whnf book t
    Op2 o a b -> whnfOp2 book o a b
    Op1 o a -> whnfOp1 book o a
    Pri p -> Pri p
    -- Eql t a b   -> whnfEql book t a b
    Rwt e f -> whnf book f -- Rwt reduces to just the body
    -- λ-Match constructors are values, they only reduce when applied
    Log s x -> whnfLog book s x
    _ -> term

-- -- Normalizes a let binding
whnfLet :: Book -> Expr -> Body -> Expr
whnfLet book v f = whnf book (f v)

-- Normalizes a use binding (inlines the value directly)
whnfUse :: Book -> Expr -> Body -> Expr
whnfUse book v f = whnf book (f v)

-- -- Normalizes a reference using guarded deref
whnfRef :: Book -> Name -> Int -> Expr
whnfRef book k i =
  if i == 0
    then Ref k i
    else case getDefn book k of
      Just (False, term, _) -> whnf book $ deref book k i (LHS SZ id) term
      _ -> Ref k 0

-- Normalizes a fixpoint
whnfFix :: Book -> String -> Body -> Expr
whnfFix book k f = whnf book (f (Fix k f))

-- -- Normalizes an application
whnfApp :: Book -> Expr -> Expr -> Expr
whnfApp book f x =
  case whnf book f of
    Lam _ t f' -> whnfAppLam book f' x
    Pri p -> whnfAppPri book p x
    -- λ-Match applications
    UniM f -> whnfUniM book x f
    BitM f t -> whnfBitM book x f t
    NatM z s -> whnfNatM book x z s
    LstM n c -> whnfLstM book x n c
    EnuM c e -> whnfEnuM book x c e
    SigM f -> whnfSigM book x f
    SupM l f -> whnfSupM book x l f
    EqlM f -> whnfEqlM book x f
    Frk{} -> error "unreachable"
    f' -> App f' x

-- -- Normalizes a lambda application
whnfAppLam :: Book -> Body -> Expr -> Expr
whnfAppLam book f x = whnf book (f x)

-- (&L{a b} x)
-- ----------------- APP-SUP
-- ! &L{x0 x1} = x
-- &L{(a x0) (b x1)}
whnfAppSup :: Book -> Expr -> Expr -> Expr -> Expr -> Expr
whnfAppSup book l a b x = whnf book $ Sup l (App a x) (App b x)

-- Eliminator normalizers
-- ----------------------

-- Normalizes a unit match
whnfUniM :: Book -> Expr -> Expr -> Expr
whnfUniM book x f =
  case whnf book x of
    One -> whnf book f
    x' -> App (UniM f) x'

-- Normalizes a boolean match
whnfBitM :: Book -> Expr -> Expr -> Expr -> Expr
whnfBitM book x f t =
  case whnf book x of
    Bt0 -> whnf book f
    Bt1 -> whnf book t
    x' -> App (BitM f t) x'

-- Normalizes a natural number match
whnfNatM :: Book -> Expr -> Expr -> Expr -> Expr
whnfNatM book x z s =
  case whnf book x of
    Zer -> whnf book z
    Suc n -> whnf book (App s (whnf book n))
    x' -> App (NatM z s) x'

-- Normalizes a list match
whnfLstM :: Book -> Expr -> Expr -> Expr -> Expr
whnfLstM book x n c =
  case whnf book x of
    Nil -> whnf book n
    Con h t -> whnf book (App (App c (whnf book h)) (whnf book t))
    x' -> App (LstM n c) x'

-- Normalizes a pair match
whnfSigM :: Book -> Expr -> Expr -> Expr
whnfSigM book x f =
  case whnf book x of
    Tup a b -> whnf book (App (App f (whnf book a)) (whnf book b))
    x' -> App (SigM f) x'

-- Normalizes an enum match
whnfEnuM :: Book -> Expr -> [(String, Expr)] -> Expr -> Expr
whnfEnuM book x c f =
  case whnf book x of
    Sym s -> case lookup s c of
      Just t -> whnf book t
      Nothing -> whnf book (App f (Sym s))
    x' -> App (EnuM c f) x'

-- Normalizes a superposition match
whnfSupM :: Book -> Expr -> Expr -> Expr -> Expr
whnfSupM book x l f = whnf book (App (App f x) x)

-- Normalizes an equality match
whnfEqlM :: Book -> Expr -> Expr -> Expr
whnfEqlM book x f =
  case whnf book x of
    Rfl -> whnf book f
    x' -> App (EqlM f) x'

-- Normalizes a log operation
whnfLog :: Book -> Expr -> Expr -> Expr
whnfLog book s x =
  let str :: Expr -> Maybe String
      str (red -> Nil) = Just ""
      str (red -> Con (red -> Val (CHR_V c)) cs) = do cs <- str cs; return (c : cs)
      str _ = Nothing
      red = whnf book
   in case str (whnf book s) of
        Just str -> trace str $ whnf book x
        Nothing -> whnf book x

-- Normalizes a primitive application
whnfAppPri :: Book -> PriF -> Expr -> Expr
whnfAppPri book p x =
  case whnf book x of
    x' -> case (p, x') of
      (U64_TO_CHAR, Val (U64_V n)) -> Val (CHR_V (toEnum (fromIntegral n)))
      (CHAR_TO_U64, Val (CHR_V c)) -> Val (U64_V (fromIntegral (fromEnum c)))
      (HVM_INC, t) -> t
      (HVM_DEC, t) -> t
      _ -> App (Pri p) x'

-- Numeric operations
-- ------------------

whnfOp2 :: Book -> NOp2 -> Expr -> Expr -> Expr
whnfOp2 book op a b =
  let a' = whnf book a
   in let b' = whnf book b
       in case (a', b') of
            -- Bool operations
            (Bt0, Bt0) -> case op of
              AND -> Bt0
              OR -> Bt0
              XOR -> Bt0
              EQL -> Bt1
              NEQ -> Bt0
              _ -> Op2 op a' b'
            (Bt0, Bt1) -> case op of
              AND -> Bt0
              OR -> Bt1
              XOR -> Bt1
              EQL -> Bt0
              NEQ -> Bt1
              _ -> Op2 op a' b'
            (Bt1, Bt0) -> case op of
              AND -> Bt0
              OR -> Bt1
              XOR -> Bt1
              EQL -> Bt0
              NEQ -> Bt1
              _ -> Op2 op a' b'
            (Bt1, Bt1) -> case op of
              AND -> Bt1
              OR -> Bt1
              XOR -> Bt0
              EQL -> Bt1
              NEQ -> Bt0
              _ -> Op2 op a' b'
            -- Numeric operations
            (Val (U64_V x), Val (U64_V y)) -> case op of
              ADD -> Val (U64_V (x + y))
              SUB -> Val (U64_V (x - y))
              MUL -> Val (U64_V (x * y))
              DIV -> if y == 0 then Op2 op a' b' else Val (U64_V (x `div` y))
              MOD -> if y == 0 then Op2 op a' b' else Val (U64_V (x `mod` y))
              EQL -> if x == y then Bt1 else Bt0
              NEQ -> if x /= y then Bt1 else Bt0
              LST -> if x < y then Bt1 else Bt0
              GRT -> if x > y then Bt1 else Bt0
              LEQ -> if x <= y then Bt1 else Bt0
              GEQ -> if x >= y then Bt1 else Bt0
              AND -> Val (U64_V (x .&. y))
              OR -> Val (U64_V (x .|. y))
              XOR -> Val (U64_V (x `xor` y))
              SHL -> Val (U64_V (x `shiftL` fromIntegral y))
              SHR -> Val (U64_V (x `shiftR` fromIntegral y))
              POW -> Val (U64_V (x ^ y))
            (Val (I64_V x), Val (I64_V y)) -> case op of
              ADD -> Val (I64_V (x + y))
              SUB -> Val (I64_V (x - y))
              MUL -> Val (I64_V (x * y))
              DIV -> if y == 0 then Op2 op a' b' else Val (I64_V (x `div` y))
              MOD -> if y == 0 then Op2 op a' b' else Val (I64_V (x `mod` y))
              EQL -> if x == y then Bt1 else Bt0
              NEQ -> if x /= y then Bt1 else Bt0
              LST -> if x < y then Bt1 else Bt0
              GRT -> if x > y then Bt1 else Bt0
              LEQ -> if x <= y then Bt1 else Bt0
              GEQ -> if x >= y then Bt1 else Bt0
              AND -> Val (U64_V (fromIntegral x .&. fromIntegral y))
              OR -> Val (U64_V (fromIntegral x .|. fromIntegral y))
              XOR -> Val (U64_V (fromIntegral x `xor` fromIntegral y))
              SHL -> Val (U64_V (fromIntegral x `shiftL` fromIntegral y))
              SHR -> Val (U64_V (fromIntegral x `shiftR` fromIntegral y))
              POW -> Val (I64_V (x ^ y))
            (Val (F64_V x), Val (F64_V y)) -> case op of
              ADD -> Val (F64_V (x + y))
              SUB -> Val (F64_V (x - y))
              MUL -> Val (F64_V (x * y))
              DIV -> Val (F64_V (x / y))
              MOD -> Op2 op a' b'
              EQL -> if x == y then Bt1 else Bt0
              NEQ -> if x /= y then Bt1 else Bt0
              LST -> if x < y then Bt1 else Bt0
              GRT -> if x > y then Bt1 else Bt0
              LEQ -> if x <= y then Bt1 else Bt0
              GEQ -> if x >= y then Bt1 else Bt0
              AND -> Val (U64_V (castDoubleToWord64 x .&. castDoubleToWord64 y))
              OR -> Val (U64_V (castDoubleToWord64 x .|. castDoubleToWord64 y))
              XOR -> Val (U64_V (castDoubleToWord64 x `xor` castDoubleToWord64 y))
              SHL -> Val (U64_V (castDoubleToWord64 x `shiftL` fromIntegral (castDoubleToWord64 y)))
              SHR -> Val (U64_V (castDoubleToWord64 x `shiftR` fromIntegral (castDoubleToWord64 y)))
              POW -> Val (F64_V (x ** y))
            (Val (CHR_V x), Val (CHR_V y)) -> case op of
              ADD -> Val (CHR_V (toEnum (fromEnum x + fromEnum y)))
              SUB -> Val (CHR_V (toEnum (fromEnum x - fromEnum y)))
              MUL -> Val (CHR_V (toEnum (fromEnum x * fromEnum y)))
              DIV -> if fromEnum y == 0 then Op2 op a' b' else Val (CHR_V (toEnum (fromEnum x `div` fromEnum y)))
              MOD -> if fromEnum y == 0 then Op2 op a' b' else Val (CHR_V (toEnum (fromEnum x `mod` fromEnum y)))
              EQL -> if x == y then Bt1 else Bt0
              NEQ -> if x /= y then Bt1 else Bt0
              LST -> if x < y then Bt1 else Bt0
              GRT -> if x > y then Bt1 else Bt0
              LEQ -> if x <= y then Bt1 else Bt0
              GEQ -> if x >= y then Bt1 else Bt0
              POW -> Val (CHR_V (toEnum (fromEnum x ^ fromEnum y)))
              _ -> Op2 op a' b'
            -- Nat operations: normalize to Nat/op calls
            (a'@Zer, b') -> natOp op a' b'
            (a'@(Suc _), b') -> natOp op a' b'
            (a', b'@Zer) -> natOp op a' b'
            (a', b'@(Suc _)) -> natOp op a' b'
            _ -> Op2 op a' b'
 where
  natOp op a b = case op of
    ADD -> whnf book $ App (App (Ref "Nat/add" 1) a) b
    SUB -> whnf book $ App (App (Ref "Nat/sub" 1) a) b
    MUL -> whnf book $ App (App (Ref "Nat/mul" 1) a) b
    DIV -> whnf book $ App (App (Ref "Nat/div" 1) a) b
    MOD -> whnf book $ App (App (Ref "Nat/mod" 1) a) b
    POW -> whnf book $ App (App (Ref "Nat/pow" 1) a) b
    EQL -> whnf book $ App (App (Ref "Nat/eql" 1) a) b
    NEQ -> whnf book $ App (App (Ref "Nat/neq" 1) a) b
    LST -> whnf book $ App (App (Ref "Nat/lst" 1) a) b
    GRT -> whnf book $ App (App (Ref "Nat/grt" 1) a) b
    LEQ -> whnf book $ App (App (Ref "Nat/leq" 1) a) b
    GEQ -> whnf book $ App (App (Ref "Nat/geq" 1) a) b
    _ -> Op2 op a b

whnfOp1 :: Book -> NOp1 -> Expr -> Expr
whnfOp1 book op a =
  case whnf book a of
    a' -> case a' of
      -- Bool operations
      Bt0 -> case op of
        NOT -> Bt1
        _ -> Op1 op a'
      Bt1 -> case op of
        NOT -> Bt0
        _ -> Op1 op a'
      -- Numeric operations
      Val (U64_V x) -> case op of
        NOT -> Val (U64_V (complement x))
        NEG -> Op1 op a'
      Val (I64_V x) -> case op of
        NOT -> Val (U64_V (complement (fromIntegral x)))
        NEG -> Val (I64_V (-x))
      Val (F64_V x) -> case op of
        NOT -> Val (U64_V (complement (castDoubleToWord64 x)))
        NEG -> Val (F64_V (-x))
      _ -> Op1 op a'

-- Left-Hand Side (LHS)
-- --------------------

lhsCtrNew :: (Expr -> Expr) -> SNat n -> Arg n -> (Expr -> Arg n)
lhsCtrNew l SZ ctr = \k -> App (l k) ctr
lhsCtrNew l (SS n') ctr = lhsCtrNew l n' . ctr

lhsCtrExt :: SNat k -> (Expr -> Arg (S k)) -> SNat n -> Arg n -> Arg (S (Add n k))
lhsCtrExt _ l SZ ctr = l ctr
lhsCtrExt k l (SS n') ctr = lhsCtrExt k l n' . ctr

lhsCtr :: LHS -> SNat n -> Arg n -> LHS
lhsCtr (LHS k l) n ctr = case k of
  SZ -> LHS n (lhsCtrNew l n ctr)
  SS k' -> LHS (addSNat n k') (lhsCtrExt k' l n ctr)

getArgs :: Expr -> [Expr] -> [Expr]
getArgs (App f a) acc = getArgs f (a : acc)
getArgs t acc = t : acc

lhsToList :: LHS -> [Expr]
lhsToList (LHS k l) = case k of
  SZ -> getArgs (l Era) []
  SS _ -> [] -- unreachable per original spec

-- Guarded Deref
-- -------------

deref :: Book -> String -> Int -> LHS -> Expr -> Expr
deref book k i lhs body =
  case body of
    EmpM ->
      Lam "x" Nothing $ \x -> derefUndo book k i lhs EmpM x
    UniM f ->
      Lam "x" Nothing $ \x -> case whnf book x of
        One -> deref book k i (lhsCtr lhs SZ One) f
        x' -> derefUndo book k i lhs (UniM f) x'
    BitM f t ->
      Lam "x" Nothing $ \x -> case whnf book x of
        Bt0 -> deref book k i (lhsCtr lhs SZ Bt0) f
        Bt1 -> deref book k i (lhsCtr lhs SZ Bt1) t
        x' -> derefUndo book k i lhs (BitM f t) x'
    NatM z s ->
      Lam "x" Nothing $ \x -> case whnf book x of
        Zer -> deref book k i (lhsCtr lhs SZ Zer) z
        Suc xp -> App (deref book k i (lhsCtr lhs (SS SZ) Suc) s) xp
        x' -> derefUndo book k i lhs (NatM z s) x'
    LstM n c ->
      Lam "x" Nothing $ \x -> case whnf book x of
        Nil -> deref book k i (lhsCtr lhs SZ Nil) n
        Con h t' -> App (App (deref book k i (lhsCtr lhs (SS (SS SZ)) (\h' -> Con h)) c) h) t'
        x' -> derefUndo book k i lhs (LstM n c) x'
    SigM f ->
      Lam "x" Nothing $ \x -> case whnf book x of
        Tup a b -> App (App (deref book k i (lhsCtr lhs (SS (SS SZ)) Tup) f) a) b
        x' -> derefUndo book k i lhs (SigM f) x'
    Lam n t f ->
      Lam n t $ \x -> deref book k i (lhsCtr lhs SZ x) (f x)
    t -> t

derefUndo :: Book -> String -> Int -> LHS -> Expr -> Expr -> Expr
derefUndo book k i (LHS SZ l) _ x = App (l (Ref k 0)) x
derefUndo book k i (LHS (SS n) l) body x = deref book k i (LHS n (l x)) body

-- Forcing
-- =======

--- Evaluates terms that whnf won't, including:
--- - Injective Refs (whnf skips them for pretty printing)
force :: Book -> Expr -> Expr
force book term =
  -- trace ("force: " ++ show term) $
  case whnf book term of
    term' -> case cut fn of
      Ref k i -> case getDefn book k of
        Just (True, fn', _) -> force book $ foldl App fn' xs
        _ -> term'
      term' -> term'
     where
      (fn, xs) = collectApps term' []

-- Normalization
-- =============

normal :: Book -> Expr -> Expr
normal book term =
  -- trace ("normal: " ++ show term ++ " ~> " ++ show (whnf book term)) $
  case whnf book term of
    Var k i -> Var k i
    Ref k i -> Ref k i
    Sub t -> t
    Fix k f -> Fix k (normal book . f . Sub)
    Let k t v f -> Let k (fmap (normal book) t) (normal book v) (normal book . f . Sub)
    Use k v f -> Use k (normal book v) (normal book . f . Sub)
    Set -> Set
    Chk x t -> Chk (normal book x) (normal book t)
    Tst x -> Tst (normal book x)
    Emp -> Emp
    EmpM -> EmpM
    Uni -> Uni
    One -> One
    UniM f -> UniM (normal book f)
    Bit -> Bit
    Bt0 -> Bt0
    Bt1 -> Bt1
    BitM f t -> BitM (normal book f) (normal book t)
    Nat -> Nat
    Zer -> Zer
    Suc n -> Suc (normal book n)
    NatM z s -> NatM (normal book z) (normal book s)
    Lst t -> Lst (normal book t)
    Nil -> Nil
    Con h t -> Con (normal book h) (normal book t)
    LstM n c -> LstM (normal book n) (normal book c)
    Enu s -> Enu s
    Sym s -> Sym s
    EnuM c e -> EnuM (map (second (normal book)) c) (normal book e)
    Sig a b -> Sig (normal book a) (normal book b)
    Tup a b -> Tup (normal book a) (normal book b)
    SigM f -> SigM (normal book f)
    All a b -> All (normal book a) (normal book b)
    Lam k t f -> Lam k (fmap (normal book) t) (normal book . f . Sub)
    App f x -> App (normal book f) (normal book x)
    Eql t a b -> Eql (normal book t) (normal book a) (normal book b)
    Rfl -> Rfl
    EqlM f -> EqlM (normal book f)
    Rwt e f -> Rwt (normal book e) (normal book f)
    Loc l t -> Loc l (normal book t)
    Log s x -> Log (normal book s) (normal book x)
    Era -> Era
    Sup l a b -> Sup l (normal book a) (normal book b)
    SupM l f -> SupM (normal book l) (normal book f)
    Frk l a b -> error "Fork interactions unsupported in Haskell"
    Num t -> Num t
    Val v -> Val v
    Op2 o a b -> Op2 o (normal book a) (normal book b)
    Op1 o a -> Op1 o (normal book a)
    Pri p -> Pri p
    Met{} -> error "not-supported"
    Pat{} -> error "not-supported"

normalCtx :: Book -> SCtx -> SCtx
normalCtx book (SCtx ctx) = SCtx (map normalAnn ctx)
 where
  normalAnn (k, v, t) = (k, normal book v, normal book t)
