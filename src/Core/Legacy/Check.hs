{-./Type.hs-}
{-./Show.hs-}
{-# LANGUAGE ViewPatterns #-}

module Core.Legacy.Check where

import Control.Monad (foldM, unless)
import Data.List (find)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Set qualified as S
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import System.IO.Unsafe (unsafePerformIO)

import Debug.Trace

import Core.Legacy.Bind
import Core.Legacy.Equal
import Core.Legacy.WHNF
import Core.Rewrite
import Core.Show
import Core.Sort

-- Utils
-- -------

extend :: SCtx -> Name -> Expr -> Expr -> SCtx
extend (SCtx ctx) k v t = SCtx (ctx ++ [(k, v, t)])

-- Check if a Sigma type represents a constructor
-- Constructor types are sigma lists that:
-- 1. Start with an Enum (constructor tag)
-- 2. End with Unit (by convention)
isConstructorSigma :: Book -> Expr -> Bool
isConstructorSigma book (Sig a b) = case force book a of
  Enu _ -> endsWithUnit b 0
  _ -> False
 where
  -- Check if the sigma chain ends with Unit (type or value)
  endsWithUnit :: Expr -> Int -> Bool
  endsWithUnit _ depth | depth > 10 = False -- Prevent infinite recursion
  endsWithUnit (Lam _ _ f) d = endsWithUnit (f (Var "_" 0)) (d + 1)
  endsWithUnit (App f _) d = endsWithUnit f (d + 1)
  endsWithUnit Uni _ = True -- Unit type
  endsWithUnit One _ = True -- Unit value ()
  endsWithUnit (Sig _ b') d = endsWithUnit b' (d + 1)
  -- Handle EnuM (enum match) - check all branches
  endsWithUnit (EnuM cases df) d =
    all (\(_, branch) -> endsWithUnit branch (d + 1)) cases
      && case df of
        Lam _ _ f -> endsWithUnit (f (Var "_" 0)) (d + 1)
        _ -> endsWithUnit df (d + 1)
  -- Handle Use expressions
  endsWithUnit (Use _ _ f) d = endsWithUnit (f (Var "_" 0)) (d + 1)
  endsWithUnit _ _ = False
isConstructorSigma _ _ = False

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> SCtx -> Expr -> Result Expr
infer d span book@(Book defs names) ctx term =
  case term of
    -- x : T in ctx
    -- ------------ infer-Var
    -- ctx |- x : T
    Var k i -> do
      let SCtx ks = ctx
      if i < length ks
        then
          let (_, _, typ) = ks !! i
           in Done typ
        else Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- x:T in book
    -- ------------ infer-Ref
    -- ctx |- x : T
    Ref k i -> do
      case getDefn book k of
        Just (_, _, typ) -> Done typ
        Nothing -> Fail $ Undefined span (normalCtx book ctx) k Nothing

    -- ctx |- x : T
    -- ------------ infer-Sub
    -- ctx |- x : T
    Sub x -> do
      infer d span book ctx x

    -- ctx        |- t : Set
    -- ctx        |- v : t
    -- ctx, v : T |- f : T
    -- -------------------------- infer-Let
    -- ctx |- (k : T = v ; f) : T
    Let k t v f -> case t of
      Just t -> do
        check d span book ctx t Set
        check d span book ctx v t
        infer (d + 1) span book (extend ctx k (Var k d) t) (f (Var k d))
      Nothing -> do
        vT <- infer d span book ctx v
        infer (d + 1) span book (extend ctx k (Var k d) vT) (f (Var k d))

    -- ctx |- f(v) : T
    -- -------------------------- infer-Use
    -- ctx |- (use k = v ; f) : T
    Use k v f -> do
      infer d span book ctx (f v)

    -- Can't infer Fix
    Fix k f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- t : Set
    -- ctx |- v : t
    -- ------------------- infer-Chk
    -- ctx |- (v :: t) : t
    Chk v t -> do
      check d span book ctx t Set
      check d span book ctx v t
      Done t

    -- Can't infer Trust
    Tst _ -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ---------------- Set
    -- ctx |- Set : Set
    Set -> do
      Done Set

    -- ctx |-
    -- ------------------ Emp
    -- ctx |- Empty : Set
    Emp -> do
      Done Set

    -- Can't infer EmpM
    EmpM -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ----------------- Uni
    -- ctx |- Unit : Set
    Uni -> do
      Done Set

    -- ctx |-
    -- ---------------- One
    -- ctx |- () : Unit
    One -> do
      Done Uni

    -- Can't infer UniM
    UniM f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ----------------- Bit
    -- ctx |- Bool : Set
    Bit -> do
      Done Set

    -- ctx |-
    -- ------------------- Bt0
    -- ctx |- False : Bool
    Bt0 -> do
      Done Bit

    -- ctx |-
    -- ------------------ Bt1
    -- ctx |- True : Bool
    Bt1 -> do
      Done Bit

    -- Can't infer BitM
    BitM f t -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ---------------- Nat
    -- ctx |- Nat : Set
    Nat -> do
      Done Set

    -- ctx |-
    -- --------------- Zer
    -- ctx |- 0n : Nat
    Zer -> do
      Done Nat

    -- ctx |- n : Nat
    -- ----------------- Suc
    -- ctx |- 1n+n : Nat
    Suc n -> do
      check d span book ctx n Nat
      Done Nat

    -- Can't infer NatM
    NatM z s -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- T : Set
    -- ---------------- Lst
    -- ctx |- T[] : Set
    Lst t -> do
      check d span book ctx t Set
      Done Set

    -- Can't infer Nil
    Nil -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer Con
    Con h t -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer LstM
    LstM n c -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ---------------------- Enu
    -- ctx |- enum{...} : Set
    Enu s -> do
      Done Set

    -- ctx |- &s in enum{...}
    -- ---------------------- Sym
    -- ctx |- &s : enum{...}
    Sym s -> do
      let bookEnums = [Enu tags | (k, (_, Sig (Enu tags) _, Set)) <- M.toList defs]
      case find isEnuWithTag bookEnums of
        Just t -> Done t
        Nothing -> Fail $ Undefined span (normalCtx book ctx) ("@" ++ s) Nothing
     where
      isEnuWithTag (Enu tags) = s `elem` tags
      isEnuWithTag _ = False

    -- Can't infer EnuM
    EnuM cs e -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- A : Set
    -- ctx |- B : ∀x:A. Set
    -- -------------------- Sig
    -- ctx |- ΣA.B : Set
    Sig a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (const Set)))
      Done Set

    -- ctx |- a : A
    -- ctx |- b : B
    -- --------------------- Tup
    -- ctx |- (a,b) : Σx:A.B
    Tup a b -> do
      aT <- infer d span book ctx a
      bT <- infer d span book ctx b
      Done (Sig aT (Lam "_" Nothing (const bT)))

    -- Can't infer SigM
    SigM f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- A : Set
    -- ctx |- B : ∀x:A. Set
    -- -------------------- All
    -- ctx |- ∀A.B : Set
    All a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (const Set)))
      Done Set

    -- ctx |- A : Set
    -- ctx, x:A |- f : B
    -- ------------------------ Lam
    -- ctx |- λx:A. f : ∀x:A. B
    Lam k t b -> case t of
      Just tk -> do
        check d span book ctx tk Set
        bT <- infer (d + 1) span book (extend ctx k (Var k d) tk) (b (Var k d))
        Done (All tk (Lam k (Just tk) (\v -> bindVarByIndex d v bT)))
      Nothing -> do
        Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- f : ∀x:A. B
    -- ctx |- x : A
    -- ------------------ App
    -- ctx |- f(x) : B(x)
    App f x -> do
      fT <- infer d span book ctx f
      case force book fT of
        All fA fB -> do
          check d span book ctx x fA
          Done (App fB x)
        _ -> do
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (normal book fT) Nothing

    -- ctx |- t : Set
    -- ctx |- a : t
    -- ctx |- b : t
    -- ---------------------- Eql
    -- ctx |- t{a == b} : Set
    Eql t a b -> do
      check d span book ctx t Set
      check d span book ctx a t
      check d span book ctx b t
      Done Set

    -- Can't infer Rfl
    Rfl -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer EqlM
    EqlM f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- e : t{a==b}
    -- ctx[a <- b] |- f : T[a <- b]
    -- ---------------------------- Rwt
    -- ctx |- rewrite e f : T
    Rwt e f -> do
      eT <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx = rewriteCtx d book a b ctx
          infer d span book rewrittenCtx f
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT) Nothing

    -- ctx |- t : T
    -- ------------ Loc
    -- ctx |- t : T
    Loc l t ->
      infer d l book ctx t
    -- Can't infer Era
    Era -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer Sup
    Sup l a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer SupM
    SupM l f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer Frk
    Frk l a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Enhanced metavariable inference
    Met n t c -> error "Metavariables not yet supported"
    -- ctx |-
    -- -------------- Num
    -- ctx |- T : Set
    Num t -> do
      Done Set

    -- ctx |-
    -- -------------- Val-U64
    -- ctx |- n : U64
    Val (U64_V v) -> do
      Done (Num U64_T)

    -- ctx |-
    -- -------------- Val-I64
    -- ctx |- n : I64
    Val (I64_V v) -> do
      Done (Num I64_T)

    -- ctx |-
    -- -------------- Val-F64
    -- ctx |- n : F64
    Val (F64_V v) -> do
      Done (Num F64_T)

    -- ctx |-
    -- --------------- Val-CHR
    -- ctx |- c : Char
    Val (CHR_V v) -> do
      Done (Num CHR_T)

    -- ctx |- a : ta
    -- ctx |- b : tb
    -- inferOp2Type op ta tb = tr
    -- --------------------------- Op2
    -- ctx |- a op b : tr
    Op2 op a b -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      inferOp2Type d span book ctx op ta tb

    -- ctx |- a : ta
    -- inferOp1Type op ta = tr
    -- ----------------------- Op1
    -- ctx |- op a : tr
    Op1 op a -> do
      ta <- infer d span book ctx a
      inferOp1Type d span book ctx op ta

    -- ctx |-
    -- -------------------------------- Pri-U64_TO_CHAR
    -- ctx |- U64_TO_CHAR : U64 -> Char
    Pri U64_TO_CHAR -> do
      Done (All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))

    -- ctx |-
    -- -------------------------------- Pri-CHAR_TO_U64
    -- ctx |- CHAR_TO_U64 : Char -> U64
    Pri CHAR_TO_U64 -> do
      Done (All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))

    -- Can't infer HVM priority change primitives
    Pri HVM_INC -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing
    Pri HVM_DEC -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- s : Char[]
    -- ctx |- x : T
    -- ------------------ Log
    -- ctx |- log s x : T
    Log s x -> do
      check d span book ctx s (Lst (Num CHR_T))
      infer d span book ctx x

    -- Pattern matching should be desugared before type checking
    Pat scruts moves cases -> do
      Fail $
        Unsupported
          span
          ctx
          ( Just
              "Pattern matching expressions should be desugared before type checking. This indicates patterns were not properly adjusted during compilation."
          )

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> SCtx -> NOp2 -> Expr -> Expr -> Result Expr
inferOp2Type d span book ctx op ta tb = do
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
    OR -> boolOrIntegerOp ta tb
    XOR -> boolOrIntegerOp ta tb
    SHL -> integerOp ta tb
    SHR -> integerOp ta tb
 where
  numericOp ta tb = case (force book ta, force book tb) of
    (Num t1, Num t2) | t1 == t2 -> Done (Num t1)
    (Nat, Nat) -> Done Nat -- Allow Nat arithmetic operations
    _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta) Nothing

  comparisonOp ta tb = case (force book ta, force book tb) of
    (Num t1, Num t2) | t1 == t2 -> Done Bit
    (Bit, Bit) -> Done Bit -- Allow Bool comparison
    (Nat, Nat) -> Done Bit -- Allow Nat comparison
    _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb) Nothing

  integerOp ta tb = case (force book ta, force book tb) of
    (Num U64_T, Num U64_T) -> Done (Num U64_T)
    (Num I64_T, Num I64_T) -> Done (Num U64_T) -- Bitwise on I64 returns U64
    (Num F64_T, Num F64_T) -> Done (Num U64_T) -- Bitwise on F64 returns U64
    (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta) Nothing -- Bitwise not supported for CHR
    _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta) Nothing

  boolOrIntegerOp ta tb = case (force book ta, force book tb) of
    (Bit, Bit) -> Done Bit -- Logical operations on booleans
    (Num U64_T, Num U64_T) -> Done (Num U64_T) -- Bitwise operations on integers
    (Num I64_T, Num I64_T) -> Done (Num U64_T)
    (Num F64_T, Num F64_T) -> Done (Num U64_T)
    _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb) Nothing

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> SCtx -> NOp1 -> Expr -> Result Expr
inferOp1Type d span book ctx op ta = case op of
  NOT -> case force book ta of
    Bit -> Done Bit -- Logical NOT on Bool
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T) -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T) -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx) Nothing -- Bitwise NOT not supported for CHR
    _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing
  NEG -> case force book ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx) Nothing -- Negation not supported for CHR
    _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing

-- continue below, don't forget the comments on EVERY type checking claude

-- Check if a term has the expected type
check :: Int -> Span -> Book -> SCtx -> Expr -> Expr -> Result ()
check d span book ctx (Loc l t) goal = check d l book ctx t goal
check d span book ctx term goal =
  case (term, force book goal) of
    -- ctx |-
    -- ------------------ Trust
    -- ctx |- trust x : T
    (Tst _, _) ->
      Done ()
    -- ctx |-
    -- ----------- Era
    -- ctx |- * : T
    (Era, _) -> do
      Done ()

    -- ctx |- t : Set
    -- ctx |- v : t
    -- ctx, x:t |- f : T
    -- ------------------------- Let
    -- ctx |- (x : t = v ; f) : T
    (Let k t v f, _) -> case t of
      Just t -> do
        check d span book ctx t Set
        check d span book ctx v t
        check (d + 1) span book (extend ctx k (Var k d) t) (f (Var k d)) goal
      Nothing -> do
        vT <- infer d span book ctx v
        check (d + 1) span book (extend ctx k (Var k d) vT) (f (Var k d)) goal

    -- ctx |- f(v) : T
    -- -------------------------- Use
    -- ctx |- (use k = v ; f) : T
    (Use k v f, _) -> do
      check d span book ctx (f v) goal

    -- ctx |-
    -- ---------------- One
    -- ctx |- () : Unit
    (One, Uni) -> do
      Done ()

    -- ctx |-
    -- ------------------- Bt0
    -- ctx |- False : Bool
    (Bt0, Bit) -> do
      Done ()

    -- ctx |-
    -- ------------------ Bt1
    -- ctx |- True : Bool
    (Bt1, Bit) -> do
      Done ()

    -- ctx |-
    -- --------------- Zer
    -- ctx |- 0n : Nat
    (Zer, Nat) -> do
      Done ()

    -- ctx |- n : Nat
    -- ----------------- Suc
    -- ctx |- 1n+n : Nat
    (Suc n, Nat) -> do
      check d span book ctx n Nat

    -- ctx |- n : t{a==b}
    -- --------------------------- Suc-Eql
    -- ctx |- 1n+n : t{1n+a==1n+b}
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      check d span book ctx n (Eql t a b)

    -- ctx |-
    -- --------------- Nil
    -- ctx |- [] : T[]
    (Nil, Lst t) -> do
      Done ()

    -- Type mismatch for Nil
    (Nil, goal) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book goal) Nothing
    -- ctx |- h : T
    -- ctx |- t : T[]
    -- ------------------ Con
    -- ctx |- h<>t : T[]
    (Con h t, Lst tT) -> do
      check d span book ctx h tT
      check d span book ctx t (Lst tT)

    -- ctx |- h : T{h1==h2}
    -- ctx |- t : T[]{t1==t2}
    -- --------------------------------- Con-Eql
    -- ctx |- h<>t : T[]{h1<>t1==h2<>t2}
    (Con h t, Eql (force book -> Lst tT) (force book -> Con h1 t1) (force book -> Con h2 t2)) -> do
      check d span book ctx h (Eql tT h1 h2)
      check d span book ctx t (Eql (Lst tT) t1 t2)

    -- ctx, x:A |- f : B
    -- ---------------------- Lam
    -- ctx |- λx. f : ∀x:A. B
    (Lam k t f, All a b) -> do
      check (d + 1) span book (extend ctx k (Var k d) a) (f (Var k d)) (App b (Var k d))

    -- ctx |-
    -- --------------------------------- EmpM-Eql-Zer-Suc
    -- ctx |- λ{} : ∀p:t{0n==1n+y}. R(p)
    (EmpM, All (force book -> Eql t (force book -> Zer) (force book -> Suc y)) rT) -> do
      Done ()

    -- ctx |-
    -- --------------------------------- EmpM-Eql-Suc-Zer
    -- ctx |- λ{} : ∀p:t{1n+x==0n}. R(p)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Zer)) rT) -> do
      Done ()

    -- ctx |- λ{} : ∀p:t{x==y}. R(p)
    -- ----------------------------------- EmpM-Eql-Suc-Suc
    -- ctx |- λ{} : ∀p:t{1n+x==1n+y}. R(p)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Suc y)) rT) -> do
      check d span book ctx EmpM (All (Eql t x y) rT)

    -- ctx |-
    -- ------------------------ EmpM-Emp
    -- ctx |- λ{} : ∀x:Empty. R
    (EmpM, All (force book -> Emp) rT) -> do
      Done ()

    -- Type mismatch for EmpM
    (EmpM, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Emp (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- ctx |- f : R({==})
    -- -------------------------------------- UniM-Eql
    -- ctx |- λ{():f} : ∀p:Unit{()==()}. R(p)
    (UniM f, All (force book -> Eql (force book -> Uni) (force book -> One) (force book -> One)) rT) -> do
      check d span book ctx f (App rT Rfl)

    -- ctx |- f : R(())
    -- --------------------------- UniM
    -- ctx |- λ{():f} : ∀x:Unit. R
    (UniM f, All (force book -> Uni) rT) -> do
      check d span book ctx f (App rT One)

    -- Type mismatch for UniM
    (UniM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Uni (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- ctx |- f : R({==})
    -- ------------------------------------------------------ BitM-Eql-Bt0-Bt0
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{False==False}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt0)) rT) -> do
      check d span book ctx f (App rT Rfl)

    -- ctx |- t : R({==})
    -- ---------------------------------------------------- BitM-Eql-Bt1-Bt1
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{True==True}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt1)) rT) -> do
      check d span book ctx t (App rT Rfl)

    -- ctx |-
    -- ----------------------------------------------------- BitM-Eql-Bt0-Bt1
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{False==True}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt1)) rT) -> do
      Done ()

    -- ctx |-
    -- ----------------------------------------------------- BitM-Eql-Bt1-Bt0
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{True==False}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt0)) rT) -> do
      Done ()

    -- ctx |- f : R(False)
    -- ctx |- t : R(True)
    -- ------------------------------------- BitM
    -- ctx |- λ{False:f;True:t} : ∀x:Bool. R
    (BitM f t, All (force book -> Bit) rT) -> do
      check d span book ctx f (App rT Bt0)
      check d span book ctx t (App rT Bt1)

    -- Type mismatch for BitM
    (BitM f t, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Bit (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- ctx |- z : R({==})
    -- ------------------------------------------- NatM-Eql-Zer-Zer
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{0n==0n}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Zer)) rT) -> do
      check d span book ctx z (App rT Rfl)

    -- ctx |- s : ∀p:Nat{a==b}. R(1n+p)
    -- ----------------------------------------------- NatM-Eql-Suc-Suc
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{1n+a==1n+b}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc a) (force book -> Suc b)) rT) -> do
      check d span book ctx s (All (Eql Nat a b) (Lam "p" Nothing (App rT . Suc)))

    -- ctx |-
    -- --------------------------------------------- NatM-Eql-Zer-Suc
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{0n==1n+_}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Suc _)) rT) -> do
      Done ()

    -- ctx |-
    -- --------------------------------------------- NatM-Eql-Suc-Zer
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{1n+_==0n}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc _) (force book -> Zer)) rT) -> do
      Done ()

    -- ctx |- z : R(0n)
    -- ctx |- s : ∀p:Nat. R(1n+p)
    -- -------------------------------- NatM
    -- ctx |- λ{0n:z;1n+:s} : ∀x:Nat. R
    (NatM z s, All (force book -> Nat) rT) -> do
      check d span book ctx z (App rT Zer)
      check d span book ctx s (All Nat (Lam "p" Nothing (App rT . Suc)))

    -- Type mismatch for NatM
    (NatM z s, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Nat (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- ctx |- n : R({==})
    -- ------------------------------------------ LstM-Eql-Nil-Nil
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{[]==[]}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Nil)) rT) -> do
      check d span book ctx n (App rT Rfl)

    -- ctx |- c : ∀hp:T{h1==h2}. ∀tp:T[]{t1==t2}. R(hp<>tp)
    -- ---------------------------------------------------- LstM-Eql-Con-Con
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{h1<>t1==h2<>t2}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con h1 t1) (force book -> Con h2 t2)) rT) -> do
      check
        d
        span
        book
        ctx
        c
        ( All
            (Eql a h1 h2)
            ( Lam
                "hp"
                Nothing
                ( \hp ->
                    All
                      (Eql (Lst a) t1 t2)
                      ( Lam
                          "tp"
                          Nothing
                          (App rT . Con hp)
                      )
                )
            )
        )

    -- ctx |-
    -- -------------------------------------------- LstM-Eql-Nil-Con
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{[]==_<>_}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Con _ _)) rT) -> do
      Done ()

    -- ctx |-
    -- -------------------------------------------- LstM-Eql-Con-Nil
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{_<>_==[]}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con _ _) (force book -> Nil)) rT) -> do
      Done ()

    -- ctx |- n : R([])
    -- ctx |- c : ∀h:T. ∀t:T[]. R(h<>t)
    -- -------------------------------- LstM
    -- ctx |- λ{[]:n;<>:c} : ∀x:T[]. R
    (LstM n c, All (force book -> Lst a) rT) -> do
      check d span book ctx n (App rT Nil)
      check d span book ctx c $ All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (App rT . Con h))))

    -- Type mismatch for LstM
    (LstM n c, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Lst (Var "_" 0)) (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- s ∈ tags
    -- ---------------------- Sym
    -- ctx |- &s : enum{tags}
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Enu y)) (normal book (Sym s)) Nothing

    -- s ∈ tags, s == s1, s1 == s2
    -- -------------------------------- Sym-Eql
    -- ctx |- &s : enum{tags}{&s1==&s2}
    (Sym s, Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) -> do
      if s `elem` syms && s == s1 && s1 == s2
        then Done ()
        else Fail $ ExprMismatch span (normalCtx book ctx) (normal book (Sym s1)) (normal book (Sym s2)) Nothing

    -- s1 == s2, (s1,t) ∈ cs => ctx |- t : R({==})
    -- s1 != s2 => ctx |-
    -- ----------------------------------------------- EnuM-Eql
    -- ctx |- λ{cs;df} : ∀p:enum{syms}{&s1==&s2}. R(p)
    (EnuM cs df, All (force book -> Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) rT) -> do
      if s1 == s2
        then case lookup s1 cs of
          Just t -> do
            check d span book ctx t (App rT Rfl)
          Nothing -> do
            check d span book ctx df (All (Enu syms) (Lam "_" Nothing (App rT)))
        else Done ()

    -- ∀(s,t) ∈ cs. ctx |- t : R(&s)
    -- not all_covered => ctx |- df : ∀x:enum{syms}. R(x)
    -- -------------------------------------------------- EnuM
    -- ctx |- λ{cs;df} : ∀x:enum{syms}. R
    (EnuM cs df, All (force book -> Enu syms) rT) -> do
      mapM_ (\(s, t) -> check d span book ctx (Sym s) (Enu syms)) cs

      mapM_ (\(s, t) -> check d span book ctx t (App rT (Sym s))) cs

      let covered_syms = map fst cs
      let all_covered =
            length covered_syms >= length syms
              && all (`elem` syms) covered_syms
      if not all_covered
        then do
          if isDefaultOne df
            then Fail $ IncompleteMatch span (normalCtx book ctx) Nothing
            else do
              let enu_type = Enu syms
              let lam_goal = All enu_type (Lam "_" Nothing (App rT))
              check d span book ctx df lam_goal
        else return ()
     where
      isDefaultOne :: Expr -> Bool
      isDefaultOne term = go (cut term)
       where
        go (Lam _ Nothing f) = go (f (Var "_" 0))
        go (Use _ _ f) = go (f (Var "_" 0))
        go One = True
        go _ = False

    -- Type mismatch for EnuM
    (EnuM cs df, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu []) (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- ctx |- f : ∀xp:A{x1==x2}. ∀yp:B(x1){y1==y2}. R((xp,yp))
    -- ------------------------------------------------------- SigM-Eql
    -- ctx |- λ{(,):f} : ∀p:ΣA.B{(x1,y1)==(x2,y2)}. R(p)
    (SigM f, All (force book -> Eql (force book -> Sig a b) (force book -> Tup x1 y1) (force book -> Tup x2 y2)) rT) -> do
      check
        d
        span
        book
        ctx
        f
        ( All
            (Eql a x1 x2)
            ( Lam
                "xp"
                Nothing
                ( \xp ->
                    All
                      (Eql (App b x1) y1 y2)
                      ( Lam
                          "yp"
                          Nothing
                          (App rT . Tup xp)
                      )
                )
            )
        )

    -- ctx |- f : ∀x:Enum. ∀y:Fields(x). R((x,y))
    -- -------------------------------------------- SigM-Constructor
    -- ctx |- λ{(,):f} : ∀p:Σ(Enum).Fields. R
    -- With constructor field mismatch hint
    (SigM f, All (force book -> sig@(Sig a b)) rT) | isConstructorSigma book sig -> do
      case check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (App rT . Tup h)))) of
        Done () -> Done ()
        Fail err -> Fail $ case err of
          TypeMismatch s c g t _ -> TypeMismatch s c g t (Just "Are you putting extra or missing constructor fields?")
          _ -> err

    -- ctx |- f : ∀x:A. ∀y:B(x). R((x,y))
    -- ----------------------------------- SigM-Regular
    -- ctx |- λ{(,):f} : ∀p:ΣA.B. R
    (SigM f, All (force book -> Sig a b) rT) -> do
      check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (App rT . Tup h))))

    -- Type mismatch for SigM
    (SigM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- ctx |- a : A
    -- ctx |- b : B(a)
    -- ------------------- Tup
    -- ctx |- (a,b) : ΣA.B
    (Tup a b, Sig aT bT) -> do
      check d span book ctx a aT
      check d span book ctx b (App bT a)

    -- ctx |- a : A{a1==a2}
    -- ctx |- b : B(a1){b1==b2}
    -- ------------------------------------- Tup-Eql
    -- ctx |- (a,b) : ΣA.B{(a1,b1)==(a2,b2)}
    (Tup a b, Eql (force book -> Sig aT bT) (force book -> Tup a1 b1) (force book -> Tup a2 b2)) -> do
      check d span book ctx a (Eql aT a1 a2)
      check d span book ctx b (Eql (App bT a1) b1 b2)

    -- equal a b
    -- --------------------- Rfl
    -- ctx |- {==} : T{a==b}
    (Rfl, Eql t a b) -> do
      if equal d book a b
        then Done ()
        else Fail $ ExprMismatch span (normalCtx book ctx) (normal book a) (normal book b) Nothing

    -- ctx[a <- b] |- f : R({==})[a <- b]
    -- ----------------------------------- EqlM
    -- ctx |- λ{{==}:f} : ∀p:T{a==b}. R(p)
    (EqlM f, All (force book -> Eql t a b) rT) -> do
      let rewrittenGoal = rewrite d book a b (App rT Rfl)
      let rewrittenCtx = rewriteCtx d book a b ctx
      check d span book rewrittenCtx f rewrittenGoal

    -- ctx, k:T |- f : T
    -- ----------------- Fix
    -- ctx |- μk. f : T
    (Fix k f, _) -> do
      check (d + 1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal

    -- ctx |-
    -- -------------- Val-U64
    -- ctx |- n : U64
    (Val v@(U64_V _), Num U64_T) -> do
      Done ()

    -- ctx |-
    -- -------------- Val-I64
    -- ctx |- n : I64
    (Val v@(I64_V _), Num I64_T) -> do
      Done ()

    -- ctx |-
    -- -------------- Val-F64
    -- ctx |- n : F64
    (Val v@(F64_V _), Num F64_T) -> do
      Done ()

    -- ctx |-
    -- --------------- Val-CHR
    -- ctx |- c : Char
    (Val v@(CHR_V _), Num CHR_T) -> do
      Done ()

    -- v1 == v2, v2 == v3
    -- --------------------- Val-Eql
    -- ctx |- v1 : T{v2==v3}
    (Val v1, Eql (force book -> Num t) (force book -> Val v2) (force book -> Val v3)) -> do
      if v1 == v2 && v2 == v3
        then Done ()
        else Fail $ ExprMismatch span (normalCtx book ctx) (normal book (Val v2)) (normal book (Val v3)) Nothing

    -- ctx |- a : ta
    -- ctx |- b : tb
    -- inferOp2Type op ta tb = tr
    -- equal tr goal
    -- --------------------------- Op2
    -- ctx |- a op b : goal
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      tr <- inferOp2Type d span book ctx op ta tb
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr) Nothing

    -- ctx |- a : ta
    -- inferOp1Type op ta = tr
    -- equal tr goal
    -- ----------------------- Op1
    -- ctx |- op a : goal
    (Op1 op a, _) -> do
      ta <- infer d span book ctx a
      tr <- inferOp1Type d span book ctx op ta
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr) Nothing

    -- ctx |- a : T
    -- ctx |- b : T
    -- ------------------ Sup
    -- ctx |- &L{a,b} : T
    (Sup l a b, _) -> do
      check d span book ctx a goal
      check d span book ctx b goal

    -- equal l l1, equal l1 l2
    -- ctx |- f : ∀ap:T{a1==a2}. ∀bp:T{b1==b2}. R(&l{ap,bp})
    -- ------------------------------------------------------ SupM-Eql
    -- ctx |- λ{&l{,}:f} : ∀p:T{&l1{a1,b1}==&l2{a2,b2}}. R(p)
    (SupM l f, All (force book -> Eql t (force book -> Sup l1 a1 b1) (force book -> Sup l2 a2 b2)) rT) -> do
      if equal d book l l1 && equal d book l1 l2
        then do
          check
            d
            span
            book
            ctx
            f
            ( All
                (Eql t a1 a2)
                ( Lam
                    "ap"
                    Nothing
                    ( \ap ->
                        All
                          (Eql t b1 b2)
                          ( Lam
                              "bp"
                              Nothing
                              (App rT . Sup l ap)
                          )
                    )
                )
            )
        else Fail $ ExprMismatch span (normalCtx book ctx) (normal book l1) (normal book l2) Nothing

    -- ctx |- l : U64
    -- ctx |- f : ∀p:T. ∀q:T. R(&l{p,q})
    -- --------------------------------- SupM
    -- ctx |- λ{&l{,}:f} : ∀x:T. R
    (SupM l f, _) -> do
      check d span book ctx l (Num U64_T)
      case force book goal of
        All xT rT -> do
          check d span book ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (App rT . Sup l p)))))
        _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "?" 0)))) Nothing

    -- ctx |- l : U64
    -- ctx |- a : T
    -- ctx |- b : T
    -- -------------------------- Frk
    -- ctx |- fork l:a else:b : T
    (Frk l a b, _) -> do
      check d span book ctx l (Num U64_T)
      check d span book ctx a goal
      check d span book ctx b goal

    -- ctx |- e : T{a==b}
    -- ctx[a <- b] |- f : goal[a <- b]
    -- ------------------------------- Rwt
    -- ctx |- rewrite e f : goal
    (Rwt e f, _) -> do
      eT <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx = rewriteCtx d book a b ctx
          let rewrittenGoal = rewrite d book a b goal
          check d span book rewrittenCtx f rewrittenGoal
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT) Nothing

    -- Pattern matching should be desugared before type checking
    (Pat{}, _) -> do
      Fail $
        Unsupported
          span
          ctx
          ( Just
              "Pattern matching expressions should be desugared before type checking. This indicates patterns were not properly adjusted during compilation."
          )

    -- ctx |- s : Char[]
    -- ctx |- x : T
    -- ------------------ Log
    -- ctx |- log s x : T
    (Log s x, _) -> do
      check d span book ctx s (Lst (Num CHR_T))
      check d span book ctx x goal

    -- ctx |- x : T
    -- ------------------ HVM_INC
    -- ctx |- HVM_INC x : T
    (App (Pri HVM_INC) x, _) ->
      check d span book ctx x goal
    -- ctx |- x : T
    -- ------------------ HVM_DEC
    -- ctx |- HVM_DEC x : T
    (App (Pri HVM_DEC) x, _) ->
      check d span book ctx x goal
    -- Type mismatch for Lam
    (Lam f t x, _) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1) Nothing
    -- ctx |- x : T
    -- ctx |- f : T -> T -> P
    -- ----------------------
    -- ctx |- (λ{&L:f} x) : P
    (App (SupM l f) x, _) -> do
      xT <- infer d span book ctx x
      check d span book ctx f (All xT (Lam "_" Nothing (\_ -> All xT (Lam "_" Nothing (const goal)))))

    -- Default case: try to infer and verify
    (term, _) -> do
      let (fn, xs) = collectApps term []
      if isLam fn
        then do
          Fail $ Unsupported span (normalCtx book ctx) Nothing
        else do
          verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> SCtx -> Expr -> Expr -> Result ()
verify d span book ctx term goal = do
  t <- infer d span book ctx term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t) Nothing
