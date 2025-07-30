{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import qualified Data.Map as M
import Data.List (find)
import Data.Maybe (fromJust)
import Control.Monad (unless)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

import Debug.Trace

import Core.Equal
import Core.Type
import Core.WHNF
import Core.Rewrite (rewrite, rewriteCtx)

-- Context
-- -------

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> Ctx -> Term -> Result (Term,Term)
infer d span book@(Book defs _) ctx term =
  trace ("- infer: " ++ show d ++ " " ++ show term) $
  case term of
    Var k i -> do
      let Ctx ks = ctx
      if i < length ks
        then let (_, _, typ) = ks !! i
             in Done (Var k i , typ)
        else Fail $ CantInfer span (normalCtx book ctx)
    Ref k i -> do
      case getDefn book k of
        Just (_, _, typ) -> Done (Ref k i , typ)
        Nothing          -> Fail $ Undefined span (normalCtx book ctx) k
    Sub x -> do
      infer d span book ctx x
    Let k t v f -> case t of
      Just t -> do
        tV      <- check d span book ctx t Set
        vV      <- check d span book ctx v t
        (fV,fT) <- infer (d+1) span book (extend ctx k (Var k d) t) (f (Var k d))
        return $ (Let k (Just tV) vV (\x -> bindVar d x fV), fT)
      Nothing -> do
        (vV,vT) <- infer d span book ctx v
        (fV,fT) <- infer (d+1) span book (extend ctx k (Var k d) vT) (f (Var k d))
        return $ (Let k Nothing vV (\x -> bindVar d x fV), fT)
    Use k v f -> do
      infer d span book ctx (f v)
    Fix k f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Chk v t -> do
      tV <- check d span book ctx t Set
      vV <- check d span book ctx v tV
      Done (Chk vV tV, tV)
    Set -> do
      Done (Set, Set)
    Emp -> do
      Done (Emp, Set)
    EmpM -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Uni -> do
      Done (Uni, Set)
    One -> do
      Done (One, Uni)
    UniM f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Bit -> do
      Done (Bit, Set)
    Bt0 -> do
      Done (Bt0, Bit)
    Bt1 -> do
      Done (Bt1, Bit)
    BitM f t -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Nat -> do
      Done (Nat, Set)
    Zer -> do
      Done (Zer, Nat)
    Suc n -> do
      nV <- check d span book ctx n Nat
      Done (Suc nV, Nat)
    NatM z s -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Lst t -> do
      tV <- check d span book ctx t Set
      Done (Lst tV, Set)
    Nil -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Con h t -> do
      Fail $ CantInfer span (normalCtx book ctx)
    LstM n c -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Enu s -> do
      Done (Enu s, Set)
    Sym s -> do
      let bookEnums = [ Enu tags | (k, (_, (Sig (Enu tags) _), Set)) <- M.toList defs ]
      case find isEnuWithTag bookEnums of
        Just t  -> Done (Sym s, t)
        Nothing -> Fail $ CantInfer span (normalCtx book ctx)
        where
          isEnuWithTag (Enu tags) = s `elem` tags
          isEnuWithTag _ = False
    EnuM cs e -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Sig a b -> do
      aV <- check d span book ctx a Set
      bV <- check d span book ctx b (All aV (Lam "_" Nothing (\_ -> Set)))
      Done (Sig aV bV, Set)
    Tup a b -> do
      (aV,aT) <- infer d span book ctx a
      (bV,bT) <- infer d span book ctx b
      Done (Tup aV bV, Sig aT (Lam "_" Nothing (\_ -> bT)))
    SigM f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    All a b -> do
      aV <- check d span book ctx a Set
      bV <- check d span book ctx b (All aV (Lam "_" Nothing (\_ -> Set)))
      Done (All aV bV, Set)
    Lam k t b -> case t of
      Just tk -> do
        tkV <- check d span book ctx tk Set
        (bV,bT) <- infer (d+1) span book (extend ctx k (Var k d) tkV) (b (Var k d))
        Done (Lam k (Just tkV) (\v -> bindVar d v bV), All tkV (Lam k (Just tkV) (\v -> bindVar d v bT)))
      Nothing -> do
        Fail $ CantInfer span (normalCtx book ctx)
    App f x -> do
      (fV,fT) <- infer d span book ctx f
      case force book fT of
        All fA fB -> do
          xV <- check d span book ctx x fA
          Done (App fV xV, App fB xV)
        _ -> do
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (normal book fT)
    Eql t a b -> do
      tV <- check d span book ctx t Set
      aV <- check d span book ctx a tV
      bV <- check d span book ctx b tV
      Done (Eql tV aV bV, Set)
    Rfl -> do
      Fail $ CantInfer span (normalCtx book ctx)
    EqlM f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Rwt e f -> do
      (eV,eT) <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx = rewriteCtx d book a b ctx
          (fV,fT) <- infer d span book rewrittenCtx f
          Done (Rwt eV fV, fT)
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT)
    Loc l t ->
      infer d l book ctx t
    Era -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Sup l a b -> do
      Fail $ CantInfer span (normalCtx book ctx)
    SupM l f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Frk l a b -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Met n t c -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Num t -> do
      Done (Num t, Set)
    Val (U64_V v) -> do
      Done (Val (U64_V v), Num U64_T)
    Val (I64_V v) -> do
      Done (Val (I64_V v), Num I64_T)
    Val (F64_V v) -> do
      Done (Val (F64_V v), Num F64_T)
    Val (CHR_V v) -> do
      Done (Val (CHR_V v), Num CHR_T)
    Op2 op a b -> do
      (aV,ta) <- infer d span book ctx a
      (bV,tb) <- infer d span book ctx b
      (opV,tr) <- inferOp2Type d span book ctx op aV bV ta tb
      Done (opV, tr)
    Op1 op a -> do
      (aV,ta) <- infer d span book ctx a
      (opV,tr) <- inferOp1Type d span book ctx op aV ta
      Done (opV, tr)
    Pri U64_TO_CHAR -> do
      Done (Pri U64_TO_CHAR, All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))
    Pri CHAR_TO_U64 -> do
      Done (Pri CHAR_TO_U64, All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))
    Log s x -> do
      sV <- check d span book ctx s (Lst (Num CHR_T))
      (xV,xT) <- infer d span book ctx x
      Done (Log sV xV, xT)
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Ctx -> NOp2 -> Term -> Term -> Term -> Term -> Result (Term,Term)
inferOp2Type d span book ctx op a b ta tb = do
  -- For arithmetic ops, both operands must have the same numeric type
  case op of
    ADD -> numericOp ta tb
    SUB -> numericOp ta tb
    MUL -> numericOp ta tb
    DIV -> numericOp ta tb
    MOD -> numericOp ta tb
    POW -> numericOp ta tb
    -- Comparison ops return Bool
    EQL -> comparisonOp ta tb
    NEQ -> comparisonOp ta tb
    LST -> comparisonOp ta tb
    GRT -> comparisonOp ta tb
    LEQ -> comparisonOp ta tb
    GEQ -> comparisonOp ta tb
    -- Bitwise/logical ops work on both integers and booleans
    AND -> boolOrIntegerOp ta tb
    OR  -> boolOrIntegerOp ta tb
    XOR -> boolOrIntegerOp ta tb
    SHL -> integerOp ta tb
    SHR -> integerOp ta tb
  where
    numericOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done (Op2 op a b, Num t1)
      (Nat, Nat) -> Done (Op2 op a b, Nat)  -- Allow Nat arithmetic operations
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)
    
    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done (Op2 op a b, Bit)
      (Bit, Bit) -> Done (Op2 op a b, Bit)  -- Allow Bool comparison
      (Nat, Nat) -> Done (Op2 op a b, Bit)  -- Allow Nat comparison
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)
    
    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> Done (Op2 op a b, Num U64_T)
      (Num I64_T, Num I64_T) -> Done (Op2 op a b, Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (Op2 op a b, Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)
    
    boolOrIntegerOp ta tb = case (force book ta, force book tb) of
      (Bit, Bit) -> Done (Op2 op a b, Bit)  -- Logical operations on booleans
      (Num U64_T, Num U64_T) -> Done (Op2 op a b, Num U64_T)  -- Bitwise operations on integers
      (Num I64_T, Num I64_T) -> Done (Op2 op a b, Num U64_T)
      (Num F64_T, Num F64_T) -> Done (Op2 op a b, Num U64_T)
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Ctx -> NOp1 -> Term -> Term -> Result (Term,Term)
inferOp1Type d span book ctx op a ta = case op of
  NOT -> case force book ta of
    Bit       -> Done (Op1 op a, Bit)  -- Logical NOT on Bool
    Num U64_T -> Done (Op1 op a, Num U64_T)
    Num I64_T -> Done (Op1 op a, Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Op1 op a, Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)
  NEG -> case force book ta of
    Num I64_T -> Done (Op1 op a, Num I64_T)
    Num F64_T -> Done (Op1 op a, Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)

-- Check if a term has the expected type
-- TODO: review the NEW CASES
check :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result Term
check d span book ctx (Loc l t) goal = check d l book ctx t goal 
check d span book ctx term      goal =
  trace ("- check: " ++ show d ++ " " ++ show term ++ " :: " ++ show (force book (normal book goal))) $
  case (term, force book goal) of
    (Era, _) -> do
      Done Era
    (Let k t v f, _) -> case t of
        Just t  -> do
          tV <- check d span book ctx t Set
          vV <- check d span book ctx v tV
          fV <- check (d+1) span book (extend ctx k (Var k d) tV) (f (Var k d)) goal
          Done (Let k (Just tV) vV (\x -> bindVar d x fV))
        Nothing -> do
          (vV,vT) <- infer d span book ctx v
          fV <- check (d+1) span book (extend ctx k (Var k d) vT) (f (Var k d)) goal
          Done (Let k Nothing vV (\x -> bindVar d x fV))
    (Use k v f, _) -> do
      check d span book ctx (f v) goal
    (One, Uni) -> do
      Done One
    (Bt0, Bit) -> do
      Done Bt0
    (Bt1, Bit) -> do
      Done Bt1
    (Zer, Nat) -> do
      Done Zer
    (Suc n, Nat) -> do
      nV <- check d span book ctx n Nat
      Done (Suc nV)
    -- NEW CASE:
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      nV <- check d span book ctx n (Eql t a b)
      Done (Suc nV)
    (Nil, Lst t) -> do
      Done Nil
    (Nil, goal) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book goal)
    (Con h t, Lst tT) -> do
      hV <- check d span book ctx h tT
      tV <- check d span book ctx t (Lst tT)
      Done (Con hV tV)
    -- NEW CASE:
    (Con h t, Eql (force book -> Lst tT) (force book -> Con h1 t1) (force book -> Con h2 t2)) -> do
      hV <- check d span book ctx h (Eql tT h1 h2)
      tV <- check d span book ctx t (Eql (Lst tT) t1 t2)
      Done (Con hV tV)
    (Lam k t f, All a b) -> trace ("OXI: " ++ show (f (Var k d))) $ do
      fV <- check (d+1) span book (extend ctx k (Var k d) a) (f (Var k d)) (App b (Var k d))
      Done (Lam k t (\v -> bindVar d v fV))
    (EmpM, All (force book -> Eql t (force book -> Zer) (force book -> Suc y)) rT) -> do
      Done EmpM
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Zer)) rT) -> do
      Done EmpM
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Suc y)) rT) -> do
      check d span book ctx EmpM (All (Eql t x y) rT)
    (EmpM, All (force book -> Emp) rT) -> do
      Done EmpM
    (EmpM, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Emp (Lam "_" Nothing (\_ -> Set))))
    -- NEW CASE:
    (UniM f, All (force book -> Eql (force book -> Uni) (force book -> One) (force book -> One)) rT) -> do
      fV <- check d span book ctx f (App rT Rfl)
      Done (UniM fV)
    (UniM f, All (force book -> Uni) rT) -> do
      fV <- check d span book ctx f (App rT One)
      Done (UniM fV)
    (UniM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Uni (Lam "_" Nothing (\_ -> Set))))
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt0)) rT) -> do
      fV <- check d span book ctx f (App rT Rfl)
      Done (BitM fV t)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt1)) rT) -> do
      tV <- check d span book ctx t (App rT Rfl)
      Done (BitM f tV)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt1)) rT) -> do
      Done (BitM f t)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt0)) rT) -> do
      Done (BitM f t)
    (BitM f t, All (force book -> Bit) rT) -> do
      fV <- check d span book ctx f (App rT Bt0)
      tV <- check d span book ctx t (App rT Bt1)
      Done (BitM fV tV)
    (BitM f t, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Bit (Lam "_" Nothing (\_ -> Set))))
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Zer)) rT) -> do
      zV <- check d span book ctx z (App rT Rfl)
      Done (NatM zV s)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc a) (force book -> Suc b)) rT) -> do
      sV <- check d span book ctx s (All (Eql Nat a b) (Lam "p" Nothing (\p -> App rT (Suc p))))
      Done (NatM z sV)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Suc _)) rT) -> do
      Done (NatM z s)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc _) (force book -> Zer)) rT) -> do
      Done (NatM z s)
    (NatM z s, All (force book -> Nat) rT) -> do
      zV <- check d span book ctx z (App rT Zer)
      sV <- check d span book ctx s (All Nat (Lam "p" Nothing (\p -> App rT (Suc p))))
      Done (NatM zV sV)
    (NatM z s, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Nat (Lam "_" Nothing (\_ -> Set))))
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Nil)) rT) -> do
      nV <- check d span book ctx n (App rT Rfl)
      Done (LstM nV c)
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con h1 t1) (force book -> Con h2 t2)) rT) -> do
      cV <- check d span book ctx c (All (Eql a h1 h2) (Lam "hp" Nothing (\hp -> 
        All (Eql (Lst a) t1 t2) (Lam "tp" Nothing (\tp -> 
          App rT (Con hp tp))))))
      Done (LstM n cV)
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Con _ _)) rT) -> do
      Done (LstM n c)
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con _ _) (force book -> Nil)) rT) -> do
      Done (LstM n c)
    (LstM n c, All (force book -> Lst a) rT) -> do
      nV <- check d span book ctx n (App rT Nil)
      cV <- check d span book ctx c $ All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (\t -> App rT (Con h t)))))
      Done (LstM nV cV)
    (LstM n c, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Lst (Var "_" 0)) (Lam "_" Nothing (\_ -> Set))))
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done (Sym s)
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Enu y)) (normal book (Sym s))
    -- NEW CASE:
    (Sym s, Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) -> do
      if s `elem` syms && s == s1 && s1 == s2
        then Done (Sym s)
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Sym s1)) (normal book (Sym s2))
    -- NEW CASE:
    (EnuM cs df, All (force book -> Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) rT) -> do
      if s1 == s2
        then case lookup s1 cs of
          Just t -> do
            tV <- check d span book ctx t (App rT Rfl)
            Done (EnuM (map (\(s,t) -> if s == s1 then (s,tV) else (s,t)) cs) df)
          Nothing -> do
            dfV <- check d span book ctx df (All (Enu syms) (Lam "_" Nothing (\v -> App rT v)))
            Done (EnuM cs dfV)
        else Done (EnuM cs df)
    (EnuM cs df, All (force book -> Enu syms) rT) -> do
      csV <- mapM (\(s, t) -> do
        tV <- check d span book ctx t (App rT (Sym s))
        return (s, tV)) cs
      let covered_syms = map fst cs
      let all_covered = length covered_syms >= length syms
                     && all (`elem` syms) covered_syms
      dfV <- if not all_covered
        then do
          case df of
            (cut -> Lam k Nothing (unlam k d -> One)) -> do
              Fail $ IncompleteMatch span (normalCtx book ctx)
            otherwise -> do
              let enu_type = Enu syms
              let lam_goal = All enu_type (Lam "_" Nothing (\v -> App rT v))
              check d span book ctx df lam_goal
        else return df
      Done (EnuM csV dfV)
    (EnuM cs df, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu []) (Lam "_" Nothing (\_ -> Set))))
    -- NEW CASE:
    (SigM f, All (force book -> Eql (force book -> Sig a b) (force book -> Tup x1 y1) (force book -> Tup x2 y2)) rT) -> do
      fV <- check d span book ctx f (All (Eql a x1 x2) (Lam "xp" Nothing (\xp -> 
        All (Eql (App b x1) y1 y2) (Lam "yp" Nothing (\yp -> 
          App rT (Tup xp yp))))))
      Done (SigM fV)
    (SigM f, All (force book -> Sig a b) rT) -> do
      fV <- check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (\t -> App rT (Tup h t)))))
      Done (SigM fV)
    (SigM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> Set))))
    (Tup a b, Sig aT bT) -> do
      aV <- check d span book ctx a aT
      bV <- check d span book ctx b (App bT aV)
      Done (Tup aV bV)
    -- NEW CASE:
    (Tup a b, Eql (force book -> Sig aT bT) (force book -> Tup a1 b1) (force book -> Tup a2 b2)) -> do
      aV <- check d span book ctx a (Eql aT a1 a2)
      bV <- check d span book ctx b (Eql (App bT a1) b1 b2)
      Done (Tup aV bV)
    (Rfl, Eql t a b) -> do
      if equal d book a b
        then Done Rfl
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book a) (normal book b)
    (EqlM f, All (force book -> Eql t a b) rT) -> do
      let rewrittenGoal = rewrite d book a b (App rT Rfl)
      let rewrittenCtx  = rewriteCtx d book a b ctx
      fV <- check d span book rewrittenCtx f rewrittenGoal
      Done (EqlM fV)
    (Fix k f, _) -> do
      fV <- check (d+1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal
      Done (Fix k (\x -> bindVar d x fV))
    (Val v@(U64_V _), Num U64_T) -> do
      Done (Val v)
    (Val v@(I64_V _), Num I64_T) -> do
      Done (Val v)
    (Val v@(F64_V _), Num F64_T) -> do
      Done (Val v)
    (Val v@(CHR_V _), Num CHR_T) -> do
      Done (Val v)
    -- NEW CASE:
    (Val v1, Eql (force book -> Num t) (force book -> Val v2) (force book -> Val v3)) -> do
      if v1 == v2 && v2 == v3
        then Done (Val v1)
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Val v2)) (normal book (Val v3))
    (Op2 op a b, _) -> do
      (aV,ta) <- infer d span book ctx a
      (bV,tb) <- infer d span book ctx b
      (opV,tr) <- inferOp2Type d span book ctx op aV bV ta tb
      if equal d book tr goal
        then Done opV
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)
    (Op1 op a, _) -> do
      (aV,ta) <- infer d span book ctx a
      (opV,tr) <- inferOp1Type d span book ctx op aV ta
      if equal d book tr goal
        then Done opV
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)
    (Sup l a b, _) -> do
      aV <- check d span book ctx a goal
      bV <- check d span book ctx b goal
      Done (Sup l aV bV)
    -- NEW CASE:
    (SupM l f, All (force book -> Eql t (force book -> Sup l1 a1 b1) (force book -> Sup l2 a2 b2)) rT) -> do
      if equal d book l l1 && equal d book l1 l2
        then do
          fV <- check d span book ctx f (All (Eql t a1 a2) (Lam "ap" Nothing (\ap -> 
                 All (Eql t b1 b2) (Lam "bp" Nothing (\bp -> 
                   App rT (Sup l ap bp))))))
          Done (SupM l fV)
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book l1) (normal book l2)
    (SupM l f, _) -> do
      lV <- check d span book ctx l (Num U64_T)
      case force book goal of
        All xT rT -> do
          fV <- check d span book ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (\q -> App rT (Sup lV p q))))))
          Done (SupM lV fV)
        _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Set))))
    (Frk l a b, _) -> do
      lV <- check d span book ctx l (Num U64_T)
      aV <- check d span book ctx a goal
      bV <- check d span book ctx b goal
      Done (Frk lV aV bV)
    (Rwt e f, _) -> do
      (eV,eT) <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx  = rewriteCtx d book a b ctx
          let rewrittenGoal = rewrite d book a b goal
          fV <- check d span book rewrittenCtx f rewrittenGoal
          Done (Rwt eV fV)
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT)
    (Pat _ _ _, _) -> do
      error "not-supported"
    (Log s x, _) -> do
      sV <- check d span book ctx s (Lst (Num CHR_T))
      xV <- check d span book ctx x goal
      Done (Log sV xV)
    (Lam f t x, _) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1)
    (App (SigM f) x, _) -> do
      (xV,xT) <- infer d span book ctx x
      case force book xT of
        Sig a b -> do
          fV <- check d span book ctx f (All a (Lam "x" Nothing (\x -> All (App b x) (Lam "y" Nothing (\y -> goal)))))
          Done (App (SigM fV) xV)
        _ -> do
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (normal book xT)
    (_, _) -> do
      verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result Term
verify d span book ctx term goal = do
  (termV,t) <- infer d span book ctx term
  if equal d book t goal
    then Done termV
    else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t)

-- Type-check all definitions in a book and return updated book with elaborated terms
checkBook :: Book -> IO Book
checkBook book@(Book defs names) = do
  let orderedDefs = [(name, fromJust (M.lookup name defs)) | name <- names]
  (success, updatedDefs) <- checkAll book orderedDefs M.empty
  unless success exitFailure
  return $ Book updatedDefs names
  where
    checkDef book term typ = do
      typV <- check 0 noSpan book (Ctx []) typ Set
      termV <- check 0 noSpan book (Ctx []) term typ
      return (termV, typV)
    checkAll :: Book -> [(Name, Defn)] -> M.Map Name Defn -> IO (Bool, M.Map Name Defn)
    checkAll _ [] accDefs = return (True, accDefs)
    checkAll bBook ((name, (span, term, typ)):rest) accDefs = do
      case checkDef bBook term typ of
        Done (termV, typV) -> do
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          let updatedDefn = (span, termV, typV)
          let updatedAccDefs = M.insert name updatedDefn accDefs
          checkAll bBook rest updatedAccDefs
        Fail e -> do
          hPutStrLn stderr $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          hPutStrLn stderr $ show e
          (_, finalDefs) <- checkAll bBook rest accDefs
          return (False, finalDefs)
