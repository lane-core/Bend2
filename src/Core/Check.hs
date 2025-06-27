{-./Type.hs-}

{-

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import qualified Data.Map as M

import Core.Equal
import Core.Normal
import Core.Rewrite
import Core.Type
import Core.WHNF
import Debug.Trace

-- Context
-- -------
-- Type checking uses Ann substitutions instead of contexts, so, the 'ctx' type
-- only exists for printing purposes. For simplicity, we just let the 'ctx' be a
-- term, and use native 'let' bindings to build its printable form.

type Context = Term -> Term

extend :: Int -> Book -> Context -> Name -> Term -> Term -> Context
extend d book ctx k t v = \f -> ctx (Let (Chk (normal 1 d book v) (normal 1 d book t)) (Lam k $ \_ -> f))

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> Context -> Subs -> Term -> Result Term
infer d span book ctx sub term =
  trace ("- infer: " ++ show term) $
  case term of
    Var k i -> do
      Fail $ CantInfer span (ctx term)
    Ref k -> do
      case deref book k of
        Just (_, _, typ) -> Done typ
        Nothing          -> Fail $ CantInfer span (ctx term)
    Sub x -> do
      infer d span book ctx sub x
    Let v f -> do
      case v of
        Chk val typ -> do
          check d span book ctx sub val typ
          infer d span book ctx sub (App f (Ann val typ))
        _ -> do
          t <- infer d span book ctx sub v
          infer d span book ctx sub (App f (Ann v t))
    Fix k f -> do
      Fail $ CantInfer span (ctx term)
    Ann v t -> do
      Done t
    Chk v t -> do
      check d span book ctx sub v t
      Done t
    Set -> do
      Done Set
    Emp -> do
      Done Set
    Efq -> do
      Fail $ CantInfer span (ctx term)
    Uni -> do
      Done Set
    One -> do
      Done Uni
    Use f -> do
      Fail $ CantInfer span (ctx term)
    Bit -> do
      Done Set
    Bt0 -> do
      Done Bit
    Bt1 -> do
      Done Bit
    Bif o i -> do
      Fail $ CantInfer span (ctx term)
    Nat -> do
      Done Set
    Zer -> do
      Done Nat
    Suc n -> do
      nT <- infer d span book ctx sub n
      case force book nT of
        Nat ->
          Done $ Nat
        Eql Nat a b ->
          Done $ Eql Nat (Suc a) (Suc b)
        _ ->
          Fail $ TypeMismatch span (ctx term) Nat (normal 1 d book nT)
    Swi z s -> do
      Fail $ CantInfer span (ctx term)
    Lst t -> do
      check d span book ctx sub t Set
      Done Set
    Nil -> do
      Fail $ CantInfer span (ctx term)
    Con h t -> do
      Fail $ CantInfer span (ctx term)
    Mat n c -> do
      Fail $ CantInfer span (ctx term)
    Enu s -> do
      Done Set
    Sym s -> do
      Fail $ CantInfer span (ctx term)
    Cse c e -> do
      Fail $ CantInfer span (ctx term)
    Sig a b -> do
      check d span book ctx sub a Set
      check d span book ctx sub b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Tup a b -> do
      aT <- infer d span book ctx sub a
      bT <- infer d span book ctx sub b
      Done $ Sig aT (Lam "_" (\_ -> bT))
    Get f -> do
      Fail $ CantInfer span (ctx term)
    All a b -> do
      check d span book ctx sub a Set
      check d span book ctx sub b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Lam _ _ -> do
      Fail $ CantInfer span (ctx term)
    App f x ->
      case (f,x) of
        -- TODO: can we generalize this to other lam forms?
        (Lam k f, Ann xv xt) -> do
          infer (d+1) span book (extend d book ctx k xt xv) sub (f (Ann xv xt))
        _ -> do
          fT <- infer d span book ctx sub f
          case force book fT of
            All fA fB -> do
              check d span book ctx sub x fA
              Done $ App fB x
            _ -> do
              Fail $ TypeMismatch span (ctx term) (All (Var "_" 0) (Lam "_" (\_ -> Var "_" 0))) fT
    Eql t a b -> do
      Done Set
    Rfl -> do
      Fail $ CantInfer span (ctx term)
    Rwt f -> do
      Fail $ CantInfer span (ctx term)
    Ind _ -> do
      Fail $ CantInfer span (ctx term)
    Frz _ -> do
      Fail $ CantInfer span (ctx term)
    Loc l t ->
      infer d l book ctx sub t
    Era -> do
      Fail $ CantInfer span (ctx term)
    Sup l a b -> do
      Fail $ CantInfer span (ctx term)
    Met _ _ _ -> do
      Fail $ CantInfer span (ctx term)
    Num _ -> do
      Done Set
    Val (U64_V _) -> do
      Done (Num U64_T)
    Val (I64_V _) -> do
      Done (Num I64_T)
    Val (F64_V _) -> do
      Done (Num F64_T)
    Val (CHR_V _) -> do
      Done (Num CHR_T)
    Op2 op a b -> do
      ta <- infer d span book ctx sub a
      tb <- infer d span book ctx sub b
      inferOp2Type d span book ctx sub op a b ta tb
    Op1 op a -> do
      ta <- infer d span book ctx sub a
      inferOp1Type d span book ctx sub op a ta
    Pri U64_TO_CHAR -> do
      Done (All (Num U64_T) (Lam "x" (\_ -> Num CHR_T)))
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Check if a term has the expected type
check :: Int -> Span -> Book -> Context -> Subs -> Term -> Term -> Result ()
check d span book ctx sub term goal =
  trace ("- check: " ++ show (normal 1 d book term) ++ " :: " ++ show (normal 1 d book goal)) $
  case (term, force book goal) of
    (Let v f, _) -> do
      case v of
        Chk val typ -> do
          check d span book ctx sub val typ
          check d span book ctx sub (App f (Ann val typ)) goal
        _ -> do
          t <- infer d span book ctx sub v
          check d span book ctx sub (App f (Ann v t)) goal
    (One, Uni) -> do
      Done ()
    (Bt0, Bit) -> do
      Done ()
    (Bt1, Bit) -> do
      Done ()
    (Zer, Nat) -> do
      Done ()
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      check d span book ctx sub n (Eql t a b)
    (Suc n, Nat) -> do
      check d span book ctx sub n Nat
    (Nil, Lst _) -> do
      Done ()
    (Nil, goal_ty) ->
      Fail $ TypeMismatch span (ctx term) (Lst (Var "_" 0)) goal_ty
    (Con h t, Lst tT) -> do
      check d span book ctx sub h tT
      check d span book ctx sub t (Lst tT)
    -- FIXME: doesn't work if we use 'All a b' because whnf removes the Ann (same for Sig)
    (Lam k f, All a (Lam _ b)) -> do
      let x = Ann (Var k d) a
      check (d+1) span book (extend d book ctx k a (Var k d)) sub (f x) (b x)
    (Efq, All a _) -> do
      case force book a of
        Emp -> Done ()
        _ -> Fail $ TypeMismatch span (ctx term) Emp a
    (Use f, All a b) -> do
      case force book a of
        Uni -> check d span book ctx sub f (App b One)
        _ -> Fail $ TypeMismatch span (ctx term) Uni a
    (Bif o i, All a b) -> do
      case force book a of
        Bit -> do
          check d span book ctx sub o (App b Bt0)
          check d span book ctx sub i (App b Bt1)
        _ -> Fail $ TypeMismatch span (ctx term) Bit a
    (Swi z s, All a b) -> do
      case force book a of
        Nat -> do
          check d span book ctx sub z (App b Zer)
          check d span book ctx sub s (All Nat (Lam "n" (\n -> App b (Suc n))))
        _ -> Fail $ TypeMismatch span (ctx term) Nat a
    (Mat n c, All a b) -> do
      case force book a of
        Lst _T -> do
          check d span book ctx sub n (App b Nil)
          check d span book ctx sub c (All _T (Lam "h" (\h -> All (Lst _T) (Lam "t" (\t -> App b (Con h t))))))
        _ -> Fail $ TypeMismatch span (ctx term) (Lst (Var "_" 0)) a
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch span (ctx term) (Enu y) (Sym s)
    (Cse c e, All a b) -> do
      case force book a of
        Enu y -> do
          let s = map fst c
          let allCasesCovered = length s == length y && all (`elem` y) s
          -- Check each case
          mapM_ (\(sym, term) -> check d span book ctx sub term (App b (Sym sym))) c
          -- Check default case
          if allCasesCovered
            then return ()
            else check d span book ctx sub e (All a b)
          Done ()
        _ -> Fail $ TypeMismatch span (ctx term) (Enu []) a
    (Get f, All a b) -> do
      case force book a of
        Sig x y -> check d span book ctx sub f (All x (Lam "x'" (\x' -> All (App y x') (Lam "y'" (\y' -> App b (Tup x' y'))))))
        _ -> Fail $ TypeMismatch span (ctx term) (Sig (Var "_" 0) (Lam "_" (\_ -> Var "_" 0))) a
    (Tup a b, Sig aT (Lam _ bT)) -> do
      check d span book ctx sub a aT
      check d span book ctx sub b (bT a)
    (Rfl, Eql t a b) -> do
      check d span book ctx sub a t
      check d span book ctx sub b t
      if equal d book a b
        then Done ()
        else Fail $ TermMismatch span (ctx term) (normal 1 d book a) (normal 1 d book b)
    (Rwt f, All a b) -> do
      case force book a of
        Eql t x y -> do
          let old = App b Rfl
          let neo = rewrite d book x y old
          -- check d span book ctx sub f neo
          trace ("rwt " ++ show x ++ " → " ++ show y ++ "\n- " ++ show old ++ "\n- " ++ show neo) $ check d span book ctx ((x,y):sub) f neo
        _ -> Fail $ TypeMismatch span (ctx term) (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0)) (normal 1 d book a)
    (Fix k f, _) -> do
      check d span book (extend d book ctx k goal (Var k d)) sub (f (Ann (Fix k f) goal)) goal

    -- (λ{T:λa.λb.t;F:λa.λb.f} x a b) :: T
    -- -----------------------------------
    -- λ{T:λa.λb.t;F:λa.λb.f} :: ∀x:X. ∀a:A. ∀b:B. T

    -- Specializes pattern-matches:
    -- (λ{...} <x:X>) :: T
    -- ------------------------------------
    -- λ{...} :: ∀v:X.(rewrite x by v in T)
    (App f x, _) ->
      if isLamApp f
        then do
          (xv,xt) <- case cut x of
            Ann xv xt -> do
              return (xv, xt)
            xv -> do
              xt <- infer d span book ctx sub xv
              return (xv, xt)
          let old_goal = All xt $ Lam "_" $ \x -> whnf 1 book goal
          let new_goal = All xt $ Lam "_" $ \x -> rewrite d book xv x (whnf 1 book goal)
          trace ("rwt " ++ show xv ++ " → ^" ++ show d ++ " !" ++
            "\n- " ++ show (normal 1 d book old_goal) ++
            "\n- " ++ show (normal 1 d book new_goal)) $
            check d span book ctx sub f new_goal
        else do
          verify d span book ctx sub term goal
    (Loc l t, _) -> do
      check d l book ctx sub t goal
    (Val (U64_V _), Num U64_T) -> do
      Done ()
    (Val (I64_V _), Num I64_T) -> do
      Done ()
    (Val (F64_V _), Num F64_T) -> do
      Done ()
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx sub a
      tb <- infer d span book ctx sub b
      tr <- inferOp2Type d span book ctx sub op a b ta tb
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (ctx term) goal tr
    (Op1 op a, _) -> do
      ta <- infer d span book ctx sub a
      tr <- inferOp1Type d span book ctx sub op a ta
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (ctx term) goal tr
    (Pat _ _ _, _) -> do
      error "not-supported"
    (_, _) -> do
      verify d span book ctx sub term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Context -> Subs -> Term -> Term -> Result ()
verify d span book ctx sub term goal = do
  t <- infer d span book ctx sub term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch span (ctx term) (normal 1 d book goal) (normal 1 d book t)

-- Utils
-- -----

isLamApp :: Term -> Bool
isLamApp (cut -> App f _) = isLamApp f
isLamApp (cut -> Lam _ _) = True
isLamApp (cut -> Efq)     = True
isLamApp (cut -> Use _)   = True
isLamApp (cut -> Bif _ _) = True
isLamApp (cut -> Swi _ _) = True
isLamApp (cut -> Mat _ _) = True
isLamApp (cut -> Cse _ _) = True
isLamApp (cut -> Get _)   = True
isLamApp (cut -> Rwt _)   = True
isLamApp _                = False

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Context -> Subs -> NOp2 -> Term -> Term -> Term -> Term -> Result Term
inferOp2Type d span book ctx sub op a b ta tb = do
  -- For arithmetic ops, both operands must have the same numeric type
  case op of
    ADD -> numericOp ta tb
    SUB -> numericOp ta tb
    MUL -> numericOp ta tb
    DIV -> numericOp ta tb
    MOD -> numericOp ta tb
    -- Comparison ops return Bool
    EQL -> comparisonOp ta tb
    NEQ -> comparisonOp ta tb
    LST -> comparisonOp ta tb
    GRT -> comparisonOp ta tb
    LEQ -> comparisonOp ta tb
    GEQ -> comparisonOp ta tb
    -- Bitwise ops require integer types
    AND -> integerOp ta tb
    OR  -> integerOp ta tb
    XOR -> integerOp ta tb
    SHL -> integerOp ta tb
    SHR -> integerOp ta tb
  where
    numericOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done (Num t1)
      _ -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb
    
    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done Bit
      _ -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb
    
    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> Done (Num U64_T)
      (Num I64_T, Num I64_T) -> Done (Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Context -> Subs -> NOp1 -> Term -> Term -> Result Term
inferOp1Type d span book ctx sub op a ta = case op of
  NOT -> case force book ta of
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (ctx (Op1 op a))  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (ctx (Op1 op a))
  NEG -> case force book ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (ctx (Op1 op a))  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (ctx (Op1 op a))

-- Check all definitions in a Book
checkBook :: Book -> Result ()
checkBook book@(Book defs) = mapM_ checkDef (M.toList defs)
  where
    checkDef (name, (_, term, typ)) = do
      check 0 noSpan book id [] term typ


NOTES FOR THE CHECKER MIGRATION:

update all pattern-matching checkers. instead of:

    (Bif o i, All a b) -> do
      case force book a of
        Bit -> do
          check d span book ctx sub o (App b Bt0)
          check d span book ctx sub i (App b Bt1)
        _ -> Fail $ TypeMismatch span (ctx term) Bit a

we will have a BitM case on infer, which:
- checks if the scrutinee is a Bit
- checks each case, rewriting the scrutinee in the goal by the case's value (Bt0/Bt1)

the same pattern should be done for all other checkers

NOTES:
- keep the type checker behavior as similar to the current one as possible
- don't forget the 'App f x' case on 'check' - important!
-}

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import qualified Data.Map as M

import Core.Equal
import Core.Normal
import Core.Rewrite
import Core.Type
import Core.WHNF
import Debug.Trace

-- Context
-- -------
-- Type checking uses Ann substitutions instead of contexts, so, the 'ctx' type
-- only exists for printing purposes. For simplicity, we just let the 'ctx' be a
-- term, and use native 'let' bindings to build its printable form.

type Context = Term -> Term

extend :: Int -> Book -> Context -> Name -> Term -> Term -> Context
extend d book ctx k t v = \f -> ctx (Let (Chk (normal 1 d book v) (normal 1 d book t)) (Lam k $ \_ -> f))

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> Context -> Subs -> Term -> Result Term
infer d span book ctx sub term =
  trace ("- infer: " ++ show term) $
  case term of
    Var k i -> do
      Fail $ CantInfer span (ctx term)
    Ref k -> do
      case deref book k of
        Just (_, _, typ) -> Done typ
        Nothing          -> Fail $ CantInfer span (ctx term)
    Sub x -> do
      infer d span book ctx sub x
    Let v f -> do
      case v of
        Chk val typ -> do
          check d span book ctx sub val typ
          infer d span book ctx sub (App f (Ann val typ))
        _ -> do
          t <- infer d span book ctx sub v
          infer d span book ctx sub (App f (Ann v t))
    Fix k f -> do
      Fail $ CantInfer span (ctx term)
    Ann v t -> do
      Done t
    Chk v t -> do
      check d span book ctx sub v t
      Done t
    Set -> do
      Done Set
    Emp -> do
      Done Set
    Efq -> do
      Fail $ CantInfer span (ctx term)
    Uni -> do
      Done Set
    One -> do
      Done Uni
    UniM _ _ -> do
      Fail $ CantInfer span (ctx term)
    Bit -> do
      Done Set
    Bt0 -> do
      Done Bit
    Bt1 -> do
      Done Bit
    BitM _ _ _ -> do
      Fail $ CantInfer span (ctx term)
    Nat -> do
      Done Set
    Zer -> do
      Done Nat
    Suc n -> do
      nT <- infer d span book ctx sub n
      case force book nT of
        Nat ->
          Done $ Nat
        Eql Nat a b ->
          Done $ Eql Nat (Suc a) (Suc b)
        _ ->
          Fail $ TypeMismatch span (ctx term) Nat (normal 1 d book nT)
    NatM _ _ _ -> do
      Fail $ CantInfer span (ctx term)
    Lst t -> do
      check d span book ctx sub t Set
      Done Set
    Nil -> do
      Fail $ CantInfer span (ctx term)
    Con h t -> do
      Fail $ CantInfer span (ctx term)
    LstM _ _ _ -> do
      Fail $ CantInfer span (ctx term)
    Enu s -> do
      Done Set
    Sym s -> do
      Fail $ CantInfer span (ctx term)
    EnuM _ _ _ -> do
      Fail $ CantInfer span (ctx term)
    Sig a b -> do
      check d span book ctx sub a Set
      check d span book ctx sub b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Tup a b -> do
      aT <- infer d span book ctx sub a
      bT <- infer d span book ctx sub b
      Done $ Sig aT (Lam "_" (\_ -> bT))
    SigM _ _ -> do
      Fail $ CantInfer span (ctx term)
    All a b -> do
      check d span book ctx sub a Set
      check d span book ctx sub b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Lam _ _ -> do
      Fail $ CantInfer span (ctx term)
    App f x ->
      case (f,x) of
        -- TODO: can we generalize this to other lam forms?
        (Lam k f, Ann xv xt) -> do
          infer (d+1) span book (extend d book ctx k xt xv) sub (f (Ann xv xt))
        _ -> do
          fT <- infer d span book ctx sub f
          case force book fT of
            All fA fB -> do
              check d span book ctx sub x fA
              Done $ App fB x
            _ -> do
              Fail $ TypeMismatch span (ctx term) (All (Var "_" 0) (Lam "_" (\_ -> Var "_" 0))) fT
    Eql t a b -> do
      Done Set
    Rfl -> do
      Fail $ CantInfer span (ctx term)
    EqlM _ _ -> do
      Fail $ CantInfer span (ctx term)
    Ind _ -> do
      Fail $ CantInfer span (ctx term)
    Frz _ -> do
      Fail $ CantInfer span (ctx term)
    Loc l t ->
      infer d l book ctx sub t
    Era -> do
      Fail $ CantInfer span (ctx term)
    Sup l a b -> do
      Fail $ CantInfer span (ctx term)
    Met _ _ _ -> do
      Fail $ CantInfer span (ctx term)
    Num _ -> do
      Done Set
    Val (U64_V _) -> do
      Done (Num U64_T)
    Val (I64_V _) -> do
      Done (Num I64_T)
    Val (F64_V _) -> do
      Done (Num F64_T)
    Val (CHR_V _) -> do
      Done (Num CHR_T)
    Op2 op a b -> do
      ta <- infer d span book ctx sub a
      tb <- infer d span book ctx sub b
      inferOp2Type d span book ctx sub op a b ta tb
    Op1 op a -> do
      ta <- infer d span book ctx sub a
      inferOp1Type d span book ctx sub op a ta
    Pri U64_TO_CHAR -> do
      Done (All (Num U64_T) (Lam "x" (\_ -> Num CHR_T)))
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Check if a term has the expected type
check :: Int -> Span -> Book -> Context -> Subs -> Term -> Term -> Result ()
check d span book ctx sub term goal =
  trace ("- check: " ++ show (normal 1 d book term) ++ " :: " ++ show (normal 1 d book goal)) $
  case (term, force book goal) of
    (Let v f, _) -> do
      case v of
        Chk val typ -> do
          check d span book ctx sub val typ
          check d span book ctx sub (App f (Ann val typ)) goal
        _ -> do
          t <- infer d span book ctx sub v
          check d span book ctx sub (App f (Ann v t)) goal
    (One, Uni) -> do
      Done ()
    (Bt0, Bit) -> do
      Done ()
    (Bt1, Bit) -> do
      Done ()
    (Zer, Nat) -> do
      Done ()
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      check d span book ctx sub n (Eql t a b)
    (Suc n, Nat) -> do
      check d span book ctx sub n Nat
    (Nil, Lst _) -> do
      Done ()
    (Nil, goal) ->
      Fail $ TypeMismatch span (ctx term) (Lst (Var "_" 0)) goal
    (Con h t, Lst tT) -> do
      check d span book ctx sub h tT
      check d span book ctx sub t (Lst tT)
    -- FIXME: doesn't work if we use 'All a b' because whnf removes the Ann (same for Sig)
    (Lam k f, All a (Lam _ b)) -> do
      let x = Ann (Var k d) a
      check (d+1) span book (extend d book ctx k a (Var k d)) sub (f x) (b x)
    (Efq, All a _) -> do
      case force book a of
        Emp -> Done ()
        _ -> Fail $ TypeMismatch span (ctx term) Emp a
    (UniM x f, goal) -> do
      xT <- infer d span book ctx sub x
      case force book xT of
        Uni -> do
          check d span book ctx sub f (rewrite d book x One goal)
        _ -> Fail $ TypeMismatch span (ctx x) Uni (normal 1 d book xT)
    (BitM x f t, goal) -> do
      xT <- infer d span book ctx sub x
      case force book xT of
        Bit -> do
          check d span book ctx sub f (rewrite d book x Bt0 goal)
          check d span book ctx sub t (rewrite d book x Bt1 goal)
        _ -> Fail $ TypeMismatch span (ctx x) Bit (normal 1 d book xT)
    (NatM x z s, goal) -> do
      xT <- infer d span book ctx sub x
      case force book xT of
        Nat -> do
          check d span book ctx sub z (rewrite d book x Zer goal)
          let s_goal = All Nat (Lam "p" (\p -> rewrite d book x (Suc p) goal))
          check d span book ctx sub s s_goal
        _ -> Fail $ TypeMismatch span (ctx x) Nat (normal 1 d book xT)
    (LstM x n c, goal) -> do
      xT <- infer d span book ctx sub x
      case force book xT of
        Lst a -> do
          check d span book ctx sub n (rewrite d book x Nil goal)
          let c_goal = All a (Lam "h" (\h -> All (Lst a) (Lam "t" (\t -> rewrite d book x (Con h t) goal))))
          check d span book ctx sub c c_goal
        _ -> Fail $ TypeMismatch span (ctx x) (Lst (Var "_" 0)) (normal 1 d book xT)
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch span (ctx term) (Enu y) (Sym s)
    (EnuM x cs e, goal) -> do
      xT <- infer d span book ctx sub x
      case force book xT of
        Enu syms -> do
          let covered_syms = map fst cs
          mapM_ (\(s, t) -> check d span book ctx sub t (rewrite d book x (Sym s) goal)) cs
          let all_covered = length covered_syms >= length syms && all (`elem` syms) covered_syms
          if not all_covered
            then check d span book ctx sub e goal
            else Done ()
        _ -> Fail $ TypeMismatch span (ctx x) (Enu []) (normal 1 d book xT)
    (SigM x f, goal) -> do
      xT <- infer d span book ctx sub x
      case force book xT of
        Sig a b -> do
          let f_goal = All a (Lam "h" (\h -> All (App b h) (Lam "t" (\t -> rewrite d book x (Tup h t) goal))))
          check d span book ctx sub f f_goal
        _ -> Fail $ TypeMismatch span (ctx x) (Sig (Var "_" 0) (Lam "_" (\_ -> Var "_" 0))) (normal 1 d book xT)
    (Tup a b, Sig aT (Lam _ bT)) -> do
      check d span book ctx sub a aT
      check d span book ctx sub b (bT a)
    (Rfl, Eql t a b) -> do
      check d span book ctx sub a t
      check d span book ctx sub b t
      if equal d book a b
        then Done ()
        else Fail $ TermMismatch span (ctx term) (normal 1 d book a) (normal 1 d book b)
    (EqlM x f, goal) -> do
      xT <- infer d span book ctx sub x
      case force book xT of
        Eql t a b -> do
          check d span book ctx ((a,b):sub) f (rewrite d book a b goal)
        _ -> Fail $ TypeMismatch span (ctx x) (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0)) (normal 1 d book xT)
    (Fix k f, _) -> do
      check d span book (extend d book ctx k goal (Var k d)) sub (f (Ann (Fix k f) goal)) goal
    (Loc l t, _) -> do
      check d l book ctx sub t goal
    (Val (U64_V _), Num U64_T) -> do
      Done ()
    (Val (I64_V _), Num I64_T) -> do
      Done ()
    (Val (F64_V _), Num F64_T) -> do
      Done ()
    (Val (CHR_V _), Num CHR_T) -> do
      Done ()
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx sub a
      tb <- infer d span book ctx sub b
      tr <- inferOp2Type d span book ctx sub op a b ta tb
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (ctx term) goal tr
    (Op1 op a, _) -> do
      ta <- infer d span book ctx sub a
      tr <- inferOp1Type d span book ctx sub op a ta
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (ctx term) goal tr
    (Pat _ _ _, _) -> do
      error "not-supported"
    -- (f x) :: G
    -- --------------------------------------------------- specialize
    -- f :: ∀(v : typeof x). (G where x is rewritten by v)
    (App f x, _) ->
      if isLamApp f
        then do
          (xv,xt) <- case cut x of
            Ann xv xt -> do
              return (xv, xt)
            xv -> do
              xt <- infer d span book ctx sub xv
              return (xv, xt)
          let old_goal = All xt $ Lam "_" $ \x -> whnf 1 book goal
          let new_goal = All xt $ Lam "_" $ \x -> rewrite d book xv x (whnf 1 book goal)
          trace ("rwt " ++ show xv ++ " → ^" ++ show d ++ " !" ++
            "\n- " ++ show (normal 1 d book old_goal) ++
            "\n- " ++ show (normal 1 d book new_goal)) $
            check d span book ctx sub f new_goal
        else do
          verify d span book ctx sub term goal

    (_, _) -> do
      verify d span book ctx sub term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Context -> Subs -> Term -> Term -> Result ()
verify d span book ctx sub term goal = do
  t <- infer d span book ctx sub term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch span (ctx term) (normal 1 d book goal) (normal 1 d book t)

-- Utils
-- -----

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Context -> Subs -> NOp2 -> Term -> Term -> Term -> Term -> Result Term
inferOp2Type d span book ctx sub op a b ta tb = do
  -- For arithmetic ops, both operands must have the same numeric type
  case op of
    ADD -> numericOp ta tb
    SUB -> numericOp ta tb
    MUL -> numericOp ta tb
    DIV -> numericOp ta tb
    MOD -> numericOp ta tb
    -- Comparison ops return Bool
    EQL -> comparisonOp ta tb
    NEQ -> comparisonOp ta tb
    LST -> comparisonOp ta tb
    GRT -> comparisonOp ta tb
    LEQ -> comparisonOp ta tb
    GEQ -> comparisonOp ta tb
    -- Bitwise ops require integer types
    AND -> integerOp ta tb
    OR  -> integerOp ta tb
    XOR -> integerOp ta tb
    SHL -> integerOp ta tb
    SHR -> integerOp ta tb
  where
    numericOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done (Num t1)
      _ -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb
    
    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done Bit
      _ -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb
    
    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> Done (Num U64_T)
      (Num I64_T, Num I64_T) -> Done (Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (ctx (Op2 op a b)) ta tb

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Context -> Subs -> NOp1 -> Term -> Term -> Result Term
inferOp1Type d span book ctx sub op a ta = case op of
  NOT -> case force book ta of
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (ctx (Op1 op a))  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (ctx (Op1 op a))
  NEG -> case force book ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (ctx (Op1 op a))  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (ctx (Op1 op a))

-- Check all definitions in a Book
checkBook :: Book -> Result ()
checkBook book@(Book defs) = mapM_ checkDef (M.toList defs)
  where
    checkDef (name, (_, term, typ)) = do
      check 0 noSpan book id [] term typ

-- Utils
-- -----

isLamApp :: Term -> Bool
isLamApp (cut -> App f _)    = isLamApp f
isLamApp (cut -> Lam _ _)    = True
isLamApp (cut -> Efq)        = True
isLamApp (cut -> UniM _ _)   = True
isLamApp (cut -> BitM _ _ _) = True
isLamApp (cut -> NatM _ _ _) = True
isLamApp (cut -> LstM _ _ _) = True
isLamApp (cut -> EnuM _ _ _) = True
isLamApp (cut -> SigM _ _)   = True
isLamApp (cut -> EqlM _ _)   = True
isLamApp _                   = False
