{-./Type.hs-}

-- (omitted)

-- PROBLEM: the `(λ{f} x)` form is NOT allowed on elaborated terms.  as such, in
-- the (App (Sigm f) x, _) case on check, we need to SPLIT the checked term into
-- `(F x)`, where `F` is a NEW top-level definition, defined as:
-- F : ∀x0:T0. ∀x1:T1. ... TX -> goal = λx0. λx1. ... λ{f}
-- where:
-- - the ∀'s and λ's are created for each var in the context
-- - TX is the inferred type of 'x'
-- to make this possible, we must refactor the type-checker to allow Book updates
-- as such, we'll now have:
-- - infer returns (Book, Term, Term) (updated Book, elaborated Term, inferred Type)
-- - check returns (Book, Term) (updated Book, elaborated Term)
-- write the COMPLETE refactored file below:

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import Control.Monad (unless)
import Control.Monad (unless, foldM)
import Data.List (find)
import Data.Maybe (fromJust)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Core.Bind
import Core.Equal
import Core.Rewrite
import Core.Type
import Core.WHNF

-- Utils
-- -------

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

-- Generate a fresh name for a new definition
freshName :: Book -> String -> String
freshName (Book defs _) base = go 0 where
  go n = let name = base ++ "_" ++ show (n :: Int)
         in if M.member name defs then go (n + 1) else name

-- Add a new definition to the book
addDefn :: Book -> Name -> Term -> Term -> Book
addDefn (Book defs names) name term typ = Book (M.insert name (True, term, typ) defs) (names ++ [name])

isLam :: Term -> Bool
isLam (Loc _ f) = isLam f
isLam Lam{}     = True
isLam EmpM      = True
isLam UniM{}    = True
isLam BitM{}    = True
isLam NatM{}    = True
isLam LstM{}    = True
isLam EnuM{}    = True
isLam SigM{}    = True
isLam SupM{}    = True
isLam EqlM{}    = True
isLam _         = False

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> Ctx -> Term -> Result (Book, Term, Term)
infer d span book@(Book defs names) ctx term =
  -- trace ("- infer: " ++ show d ++ " " ++ show term) $
  case term of
    Var k i -> do
      let Ctx ks = ctx
      if i < length ks
        then let (_, _, typ) = ks !! i
             in Done (book, Var k i, typ)
        else Fail $ CantInfer span (normalCtx book ctx)
    Ref k i -> do
      case getDefn book k of
        Just (_, _, typ) -> Done (book, Ref k i, typ)
        Nothing          -> Fail $ Undefined span (normalCtx book ctx) k
    Sub x -> do
      infer d span book ctx x
    Let k t v f -> case t of
      Just t -> do
        (book1, tV) <- check d span book ctx t Set
        (book2, vV) <- check d span book1 ctx v t
        (book3, fV, fT) <- infer (d+1) span book2 (extend ctx k (Var k d) t) (f (Var k d))
        return $ (book3, Let k (Just tV) vV (\x -> bindVar d x fV), fT)
      Nothing -> do
        (book1, vV, vT) <- infer d span book ctx v
        (book2, fV, fT) <- infer (d+1) span book1 (extend ctx k (Var k d) vT) (f (Var k d))
        return $ (book2, Let k Nothing vV (\x -> bindVar d x fV), fT)
    Use k v f -> do
      infer d span book ctx (f v)
    Fix k f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Chk v t -> do
      (book1, tV) <- check d span book ctx t Set
      (book2, vV) <- check d span book1 ctx v tV
      Done (book2, Chk vV tV, tV)
    Set -> do
      Done (book, Set, Set)
    Emp -> do
      Done (book, Emp, Set)
    EmpM -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Uni -> do
      Done (book, Uni, Set)
    One -> do
      Done (book, One, Uni)
    UniM f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Bit -> do
      Done (book, Bit, Set)
    Bt0 -> do
      Done (book, Bt0, Bit)
    Bt1 -> do
      Done (book, Bt1, Bit)
    BitM f t -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Nat -> do
      Done (book, Nat, Set)
    Zer -> do
      Done (book, Zer, Nat)
    Suc n -> do
      (book1, nV) <- check d span book ctx n Nat
      Done (book1, Suc nV, Nat)
    NatM z s -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Lst t -> do
      (book1, tV) <- check d span book ctx t Set
      Done (book1, Lst tV, Set)
    Nil -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Con h t -> do
      Fail $ CantInfer span (normalCtx book ctx)
    LstM n c -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Enu s -> do
      Done (book, Enu s, Set)
    Sym s -> do
      let bookEnums = [ Enu tags | (k, (_, (Sig (Enu tags) _), Set)) <- M.toList defs ]
      case find isEnuWithTag bookEnums of
        Just t  -> Done (book, Sym s, t)
        Nothing -> Fail $ Undefined span (normalCtx book ctx) ("@" ++ s)
        where
          isEnuWithTag (Enu tags) = s `elem` tags
          isEnuWithTag _ = False
    EnuM cs e -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Sig a b -> do
      (book1, aV) <- check d span book ctx a Set
      (book2, bV) <- check d span book1 ctx b (All aV (Lam "_" Nothing (\_ -> Set)))
      Done (book2, Sig aV bV, Set)
    Tup a b -> do
      (book1, aV, aT) <- infer d span book ctx a
      (book2, bV, bT) <- infer d span book1 ctx b
      Done (book2, Tup aV bV, Sig aT (Lam "_" Nothing (\_ -> bT)))
    SigM f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    All a b -> do
      (book1, aV) <- check d span book ctx a Set
      (book2, bV) <- check d span book1 ctx b (All aV (Lam "_" Nothing (\_ -> Set)))
      Done (book2, All aV bV, Set)
    Lam k t b -> case t of
      Just tk -> do
        (book1, tkV) <- check d span book ctx tk Set
        (book2, bV, bT) <- infer (d+1) span book1 (extend ctx k (Var k d) tkV) (b (Var k d))
        Done (book2, Lam k (Just tkV) (\v -> bindVar d v bV), All tkV (Lam k (Just tkV) (\v -> bindVar d v bT)))
      Nothing -> do
        Fail $ CantInfer span (normalCtx book ctx)
    App f x -> do
      (book1, fV, fT) <- infer d span book ctx f
      case force book1 fT of
        All fA fB -> do
          (book2, xV) <- check d span book1 ctx x fA
          Done (book2, App fV xV, App fB xV)
        _ -> do
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (normal book fT)
    Eql t a b -> do
      (book1, tV) <- check d span book ctx t Set
      (book2, aV) <- check d span book1 ctx a tV
      (book3, bV) <- check d span book2 ctx b tV
      Done (book3, Eql tV aV bV, Set)
    Rfl -> do
      Fail $ CantInfer span (normalCtx book ctx)
    EqlM f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Rwt e f -> do
      (book1, eV, eT) <- infer d span book ctx e
      case force book1 eT of
        Eql t a b -> do
          let rewrittenCtx = rewriteCtx d book1 a b ctx
          (book2, fV, fT) <- infer d span book1 rewrittenCtx f
          Done (book2, Rwt eV fV, fT)
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
      Done (book, Num t, Set)
    Val (U64_V v) -> do
      Done (book, Val (U64_V v), Num U64_T)
    Val (I64_V v) -> do
      Done (book, Val (I64_V v), Num I64_T)
    Val (F64_V v) -> do
      Done (book, Val (F64_V v), Num F64_T)
    Val (CHR_V v) -> do
      Done (book, Val (CHR_V v), Num CHR_T)
    Op2 op a b -> do
      (book1, aV, ta) <- infer d span book ctx a
      (book2, bV, tb) <- infer d span book1 ctx b
      (book3, opV, tr) <- inferOp2Type d span book2 ctx op aV bV ta tb
      Done (book3, opV, tr)
    Op1 op a -> do
      (book1, aV, ta) <- infer d span book ctx a
      (book2, opV, tr) <- inferOp1Type d span book1 ctx op aV ta
      Done (book2, opV, tr)
    Pri U64_TO_CHAR -> do
      Done (book, Pri U64_TO_CHAR, All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))
    Pri CHAR_TO_U64 -> do
      Done (book, Pri CHAR_TO_U64, All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))
    Log s x -> do
      (book1, sV) <- check d span book ctx s (Lst (Num CHR_T))
      (book2, xV, xT) <- infer d span book1 ctx x
      Done (book2, Log sV xV, xT)
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Ctx -> NOp2 -> Term -> Term -> Term -> Term -> Result (Book, Term, Term)
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
      (Num t1, Num t2) | t1 == t2 -> Done (book, Op2 op a b, Num t1)
      (Nat, Nat) -> Done (book, Op2 op a b, Nat)  -- Allow Nat arithmetic operations
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)
    
    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done (book, Op2 op a b, Bit)
      (Bit, Bit) -> Done (book, Op2 op a b, Bit)  -- Allow Bool comparison
      (Nat, Nat) -> Done (book, Op2 op a b, Bit)  -- Allow Nat comparison
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)
    
    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> Done (book, Op2 op a b, Num U64_T)
      (Num I64_T, Num I64_T) -> Done (book, Op2 op a b, Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (book, Op2 op a b, Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)
    
    boolOrIntegerOp ta tb = case (force book ta, force book tb) of
      (Bit, Bit) -> Done (book, Op2 op a b, Bit)  -- Logical operations on booleans
      (Num U64_T, Num U64_T) -> Done (book, Op2 op a b, Num U64_T)  -- Bitwise operations on integers
      (Num I64_T, Num I64_T) -> Done (book, Op2 op a b, Num U64_T)
      (Num F64_T, Num F64_T) -> Done (book, Op2 op a b, Num U64_T)
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Ctx -> NOp1 -> Term -> Term -> Result (Book, Term, Term)
inferOp1Type d span book ctx op a ta = case op of
  NOT -> case force book ta of
    Bit       -> Done (book, Op1 op a, Bit)  -- Logical NOT on Bool
    Num U64_T -> Done (book, Op1 op a, Num U64_T)
    Num I64_T -> Done (book, Op1 op a, Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (book, Op1 op a, Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)
  NEG -> case force book ta of
    Num I64_T -> Done (book, Op1 op a, Num I64_T)
    Num F64_T -> Done (book, Op1 op a, Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)

-- Check if a term has the expected type
-- TODO: review the NEW CASES
check :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result (Book, Term)
check d span book ctx (Loc l t) goal = check d l book ctx t goal 
check d span book ctx term      goal =
  -- trace ("- check: " ++ show d ++ " " ++ show term ++ " :: " ++ show (force book (normal book goal))) $
  case (term, force book goal) of
    (Era, _) -> do
      Done (book, Era)
    (Let k t v f, _) -> case t of
        Just t  -> do
          (book1, tV) <- check d span book ctx t Set
          (book2, vV) <- check d span book1 ctx v tV
          (book3, fV) <- check (d+1) span book2 (extend ctx k (Var k d) tV) (f (Var k d)) goal
          Done (book3, Let k (Just tV) vV (\x -> bindVar d x fV))
        Nothing -> do
          (book1, vV, vT) <- infer d span book ctx v
          (book2, fV) <- check (d+1) span book1 (extend ctx k (Var k d) vT) (f (Var k d)) goal
          Done (book2, Let k Nothing vV (\x -> bindVar d x fV))
    (Use k v f, _) -> do
      check d span book ctx (f v) goal
    (One, Uni) -> do
      Done (book, One)
    (Bt0, Bit) -> do
      Done (book, Bt0)
    (Bt1, Bit) -> do
      Done (book, Bt1)
    (Zer, Nat) -> do
      Done (book, Zer)
    (Suc n, Nat) -> do
      (book1, nV) <- check d span book ctx n Nat
      Done (book1, Suc nV)
    -- NEW CASE:
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      (book1, nV) <- check d span book ctx n (Eql t a b)
      Done (book1, Suc nV)
    (Nil, Lst t) -> do
      Done (book, Nil)
    (Nil, goal) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book goal)
    (Con h t, Lst tT) -> do
      (book1, hV) <- check d span book ctx h tT
      (book2, tV) <- check d span book1 ctx t (Lst tT)
      Done (book2, Con hV tV)
    -- NEW CASE:
    (Con h t, Eql (force book -> Lst tT) (force book -> Con h1 t1) (force book -> Con h2 t2)) -> do
      (book1, hV) <- check d span book ctx h (Eql tT h1 h2)
      (book2, tV) <- check d span book1 ctx t (Eql (Lst tT) t1 t2)
      Done (book2, Con hV tV)
    (Lam k t f, All a b) -> do
      (book1, fV) <- check (d+1) span book (extend ctx k (Var k d) a) (f (Var k d)) (App b (Var k d))
      Done (book1, Lam k t (\v -> bindVar d v fV))
    (EmpM, All (force book -> Eql t (force book -> Zer) (force book -> Suc y)) rT) -> do
      Done (book, EmpM)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Zer)) rT) -> do
      Done (book, EmpM)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Suc y)) rT) -> do
      check d span book ctx EmpM (All (Eql t x y) rT)
    (EmpM, All (force book -> Emp) rT) -> do
      Done (book, EmpM)
    (EmpM, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Emp (Lam "_" Nothing (\_ -> Set))))
    -- NEW CASE:
    (UniM f, All (force book -> Eql (force book -> Uni) (force book -> One) (force book -> One)) rT) -> do
      (book1, fV) <- check d span book ctx f (App rT Rfl)
      Done (book1, UniM fV)
    (UniM f, All (force book -> Uni) rT) -> do
      (book1, fV) <- check d span book ctx f (App rT One)
      Done (book1, UniM fV)
    (UniM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Uni (Lam "_" Nothing (\_ -> Set))))
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt0)) rT) -> do
      (book1, fV) <- check d span book ctx f (App rT Rfl)
      Done (book1, BitM fV t)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt1)) rT) -> do
      (book1, tV) <- check d span book ctx t (App rT Rfl)
      Done (book1, BitM f tV)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt1)) rT) -> do
      Done (book, BitM f t)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt0)) rT) -> do
      Done (book, BitM f t)
    (BitM f t, All (force book -> Bit) rT) -> do
      (book1, fV) <- check d span book ctx f (App rT Bt0)
      (book2, tV) <- check d span book1 ctx t (App rT Bt1)
      Done (book2, BitM fV tV)
    (BitM f t, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Bit (Lam "_" Nothing (\_ -> Set))))
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Zer)) rT) -> do
      (book1, zV) <- check d span book ctx z (App rT Rfl)
      Done (book1, NatM zV s)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc a) (force book -> Suc b)) rT) -> do
      (book1, sV) <- check d span book ctx s (All (Eql Nat a b) (Lam "p" Nothing (\p -> App rT (Suc p))))
      Done (book1, NatM z sV)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Suc _)) rT) -> do
      Done (book, NatM z s)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc _) (force book -> Zer)) rT) -> do
      Done (book, NatM z s)
    (NatM z s, All (force book -> Nat) rT) -> do
      (book1, zV) <- check d span book ctx z (App rT Zer)
      (book2, sV) <- check d span book1 ctx s (All Nat (Lam "p" Nothing (\p -> App rT (Suc p))))
      Done (book2, NatM zV sV)
    (NatM z s, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Nat (Lam "_" Nothing (\_ -> Set))))
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Nil)) rT) -> do
      (book1, nV) <- check d span book ctx n (App rT Rfl)
      Done (book1, LstM nV c)
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con h1 t1) (force book -> Con h2 t2)) rT) -> do
      (book1, cV) <- check d span book ctx c (All (Eql a h1 h2) (Lam "hp" Nothing (\hp -> 
        All (Eql (Lst a) t1 t2) (Lam "tp" Nothing (\tp -> 
          App rT (Con hp tp))))))
      Done (book1, LstM n cV)
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Con _ _)) rT) -> do
      Done (book, LstM n c)
    -- NEW CASE:
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con _ _) (force book -> Nil)) rT) -> do
      Done (book, LstM n c)
    (LstM n c, All (force book -> Lst a) rT) -> do
      (book1, nV) <- check d span book ctx n (App rT Nil)
      (book2, cV) <- check d span book1 ctx c $ All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (\t -> App rT (Con h t)))))
      Done (book2, LstM nV cV)
    (LstM n c, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Lst (Var "_" 0)) (Lam "_" Nothing (\_ -> Set))))
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done (book, Sym s)
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Enu y)) (normal book (Sym s))
    -- NEW CASE:
    (Sym s, Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) -> do
      if s `elem` syms && s == s1 && s1 == s2
        then Done (book, Sym s)
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Sym s1)) (normal book (Sym s2))
    -- NEW CASE:
    (EnuM cs df, All (force book -> Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) rT) -> do
      if s1 == s2
        then case lookup s1 cs of
          Just t -> do
            (book1, tV) <- check d span book ctx t (App rT Rfl)
            Done (book1, EnuM (map (\(s,t) -> if s == s1 then (s,tV) else (s,t)) cs) df)
          Nothing -> do
            (book1, dfV) <- check d span book ctx df (All (Enu syms) (Lam "_" Nothing (\v -> App rT v)))
            Done (book1, EnuM cs dfV)
        else Done (book, EnuM cs df)
    (EnuM cs df, All (force book -> Enu syms) rT) -> do
      (book1, csV) <- foldM (\(bk, acc) (s, t) -> do
        (bk', tV) <- check d span bk ctx t (App rT (Sym s))
        return (bk', acc ++ [(s, tV)])) (book, []) cs
      let covered_syms = map fst cs
      let all_covered = length covered_syms >= length syms
                     && all (`elem` syms) covered_syms
      (book2, dfV) <- if not all_covered
        then do
          case df of
            (cut -> Lam k Nothing (unlam k d -> One)) -> do
              Fail $ IncompleteMatch span (normalCtx book ctx)
            otherwise -> do
              let enu_type = Enu syms
              let lam_goal = All enu_type (Lam "_" Nothing (\v -> App rT v))
              check d span book1 ctx df lam_goal
        else return (book1, df)
      Done (book2, EnuM csV dfV)
    (EnuM cs df, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu []) (Lam "_" Nothing (\_ -> Set))))
    -- NEW CASE:
    (SigM f, All (force book -> Eql (force book -> Sig a b) (force book -> Tup x1 y1) (force book -> Tup x2 y2)) rT) -> do
      (book1, fV) <- check d span book ctx f (All (Eql a x1 x2) (Lam "xp" Nothing (\xp -> 
        All (Eql (App b x1) y1 y2) (Lam "yp" Nothing (\yp -> 
          App rT (Tup xp yp))))))
      Done (book1, SigM fV)
    (SigM f, All (force book -> Sig a b) rT) -> do
      (book1, fV) <- check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (\t -> App rT (Tup h t)))))
      Done (book1, SigM fV)
    (SigM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> Set))))
    (Tup a b, Sig aT bT) -> do
      (book1, aV) <- check d span book ctx a aT
      (book2, bV) <- check d span book1 ctx b (App bT aV)
      Done (book2, Tup aV bV)
    -- NEW CASE:
    (Tup a b, Eql (force book -> Sig aT bT) (force book -> Tup a1 b1) (force book -> Tup a2 b2)) -> do
      (book1, aV) <- check d span book ctx a (Eql aT a1 a2)
      (book2, bV) <- check d span book1 ctx b (Eql (App bT a1) b1 b2)
      Done (book2, Tup aV bV)
    (Rfl, Eql t a b) -> do
      if equal d book a b
        then Done (book, Rfl)
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book a) (normal book b)
    (EqlM f, All (force book -> Eql t a b) rT) -> do
      let rewrittenGoal = rewrite d book a b (App rT Rfl)
      let rewrittenCtx  = rewriteCtx d book a b ctx
      (book1, fV) <- check d span book rewrittenCtx f rewrittenGoal
      Done (book1, EqlM fV)
    (Fix k f, _) -> do
      (book1, fV) <- check (d+1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal
      Done (book1, Fix k (\x -> bindVar d x fV))
    (Val v@(U64_V _), Num U64_T) -> do
      Done (book, Val v)
    (Val v@(I64_V _), Num I64_T) -> do
      Done (book, Val v)
    (Val v@(F64_V _), Num F64_T) -> do
      Done (book, Val v)
    (Val v@(CHR_V _), Num CHR_T) -> do
      Done (book, Val v)
    -- NEW CASE:
    (Val v1, Eql (force book -> Num t) (force book -> Val v2) (force book -> Val v3)) -> do
      if v1 == v2 && v2 == v3
        then Done (book, Val v1)
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Val v2)) (normal book (Val v3))
    (Op2 op a b, _) -> do
      (book1, aV, ta) <- infer d span book ctx a
      (book2, bV, tb) <- infer d span book1 ctx b
      (book3, opV, tr) <- inferOp2Type d span book2 ctx op aV bV ta tb
      if equal d book3 tr goal
        then Done (book3, opV)
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)
    (Op1 op a, _) -> do
      (book1, aV, ta) <- infer d span book ctx a
      (book2, opV, tr) <- inferOp1Type d span book1 ctx op aV ta
      if equal d book2 tr goal
        then Done (book2, opV)
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)
    (Sup l a b, _) -> do
      (book1, aV) <- check d span book ctx a goal
      (book2, bV) <- check d span book1 ctx b goal
      Done (book2, Sup l aV bV)
    -- NEW CASE:
    (SupM l f, All (force book -> Eql t (force book -> Sup l1 a1 b1) (force book -> Sup l2 a2 b2)) rT) -> do
      if equal d book l l1 && equal d book l1 l2
        then do
          (book1, fV) <- check d span book ctx f (All (Eql t a1 a2) (Lam "ap" Nothing (\ap -> 
                 All (Eql t b1 b2) (Lam "bp" Nothing (\bp -> 
                   App rT (Sup l ap bp))))))
          Done (book1, SupM l fV)
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book l1) (normal book l2)
    (SupM l f, _) -> do
      (book1, lV) <- check d span book ctx l (Num U64_T)
      case force book1 goal of
        All xT rT -> do
          (book2, fV) <- check d span book1 ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (\q -> App rT (Sup lV p q))))))
          Done (book2, SupM lV fV)
        _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Set))))
    (Frk l a b, _) -> do
      (book1, lV) <- check d span book ctx l (Num U64_T)
      (book2, aV) <- check d span book1 ctx a goal
      (book3, bV) <- check d span book2 ctx b goal
      Done (book3, Frk lV aV bV)
    (Rwt e f, _) -> do
      (book1, eV, eT) <- infer d span book ctx e
      case force book1 eT of
        Eql t a b -> do
          let rewrittenCtx  = rewriteCtx d book1 a b ctx
          let rewrittenGoal = rewrite d book1 a b goal
          (book2, fV) <- check d span book1 rewrittenCtx f rewrittenGoal
          Done (book2, Rwt eV fV)
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT)
    (Pat _ _ _, _) -> do
      error "not-supported"
    (Log s x, _) -> do
      (book1, sV) <- check d span book ctx s (Lst (Num CHR_T))
      (book2, xV) <- check d span book1 ctx x goal
      Done (book2, Log sV xV)
    (Lam f t x, _) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1)

    (term, _) -> do
      let (fn, xs) = collectApps term []
      if isLam fn then do
        detach d span book ctx (fn,xs) goal
      else do
        verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result (Book, Term)
verify d span book ctx term goal = do
  (book1, termV, t) <- infer d span book ctx term
  if equal d book1 t goal
    then Done (book1, termV)
    else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t)

-- Type-check all definitions in a book and return updated book with elaborated terms
checkBook :: Book -> IO Book
checkBook book@(Book defs names) = do
  let orderedDefs = [(name, fromJust (M.lookup name defs)) | name <- names]
  (success, updatedBook) <- checkAll book orderedDefs
  unless success exitFailure
  return updatedBook
  where
    checkDef bk term typ = do
      (bk1, typV) <- check 0 noSpan bk (Ctx []) typ Set
      (bk2, termV) <- check 0 noSpan bk1 (Ctx []) term typ
      return (bk2, termV, typV)
    checkAll :: Book -> [(Name, Defn)] -> IO (Bool, Book)
    checkAll bk [] = return (True, bk)
    checkAll bk ((name, (inj, term, typ)):rest) = do
      case checkDef bk term typ of
        Done (bk', termV, typV) -> do
          -- putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          -- TODO: also print the type and new term
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m : " ++ show typV ++ " = " ++ show termV
          let updatedDefn = (inj, termV, typV)
          let Book defs' names' = bk'
          let updatedBook = Book (M.insert name updatedDefn defs') names'
          checkAll updatedBook rest
        Fail e -> do
          hPutStrLn stderr $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          hPutStrLn stderr $ show e
          (_, finalBook) <- checkAll bk rest
          return (False, finalBook)

-- Lifts a term in the form (λ{...} x0 x1 ...) as a new top-level definition.
detach :: Int -> Span -> Book -> Ctx -> (Term, [Term]) -> Term -> Result (Book, Term)
detach d span book (Ctx anns) (fn, xs) goal = do
  -- Infer types of all arguments, threading the book
  (book, xs) <- foldM (\ (bk, acc) x -> do
    (bk', xV, xT) <- infer d span bk (Ctx anns) x
    return (bk', acc ++ [(xV, xT)])) (book, []) xs

  -- New Fn Name: F_N
  -- New Fn Type: ∀(all_ctx)... -> ∀(args)... -> goal
  -- New Fn Term: λ(all_ctx)... -> fn
  -- Result Term: (F all_ctx_vars... args...)
  fnm <- return $ freshName book "F" -- TODO: improve
  fty <- return $ goal
  fty <- return $ foldr (\(_, xT) acc -> All xT (Lam "_" Nothing (\_ -> acc))) fty xs
  fty <- return $ bind $ foldr (\(k, _, t) acc -> All t (Lam k Nothing (\_ -> acc))) fty anns
  ftm <- return $ bind $ foldr (\(k, _, _) acc -> Lam k Nothing (\_ -> acc)) fn anns
  rtm <- return $ Ref fnm 0
  rtm <- return $ foldl App rtm $ map (\(_,v,_) -> v) anns
  rtm <- return $ foldl App rtm (map fst xs)

  -- Register and check new top-level definition
  trace ("+ " ++ fnm ++ " : " ++ show fty ++ " = " ++ show ftm) $ do
    book       <- return $ addDefn book fnm ftm fty
    (book,ftm) <- check 0 span book (Ctx []) ftm fty
    Book df nm <- return $ book
    book       <- return $ Book (M.adjust (\(inj,_,fty) -> (inj,ftm,fty)) fnm df) nm
    Done (book, rtm)
