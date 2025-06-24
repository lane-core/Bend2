{-./Type.hs-}
{-./WHNF.hs-}

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

-- Check all definitions in a Book
checkBook :: Book -> Result ()
checkBook book@(Book defs) = mapM_ checkDef (M.toList defs)
  where
    checkDef (name, (_, term, typ)) = do
      check 0 noSpan book id term typ

-- Infer the type of a term
infer :: Int -> Span -> Book -> Context -> Term -> Result Term
infer d span book ctx term =
  -- trace ("- infer: " ++ show term) $
  case term of
    Var k i -> do
      Fail $ CantInfer span (ctx term)
    Ref k -> do
      case deref book k of
        Just (_, _, typ) -> Done typ
        Nothing          -> Fail $ CantInfer span (ctx term)
    Sub x -> do
      infer d span book ctx x
    Let v f -> do
      case v of
        Chk val typ -> do
          check d span book ctx val typ
          infer d span book ctx (App f (Ann val typ))
        _ -> do
          t <- infer d span book ctx v
          infer d span book ctx (App f (Ann v t))
    Fix k f -> do
      Fail $ CantInfer span (ctx term)
    Ann v t -> do
      Done t
    Chk v t -> do
      check d span book ctx v t
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
      nT <- infer d span book ctx n
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
      check d span book ctx t Set
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
    Cse c -> do
      Fail $ CantInfer span (ctx term)
    Sig a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Tup a b -> do
      aT <- infer d span book ctx a
      bT <- infer d span book ctx b
      Done $ Sig aT (Lam "_" (\_ -> bT))
    Get f -> do
      Fail $ CantInfer span (ctx term)
    All a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Lam _ _ -> do
      Fail $ CantInfer span (ctx term)
    App f x ->
      case (f,x) of
        -- TODO: can we generalize this to other lam forms?
        (Lam k f, Ann xv xt) -> do
          infer (d+1) span book (extend d book ctx k xt xv) (f (Ann xv xt))
        _ -> do
          fT <- infer d span book ctx f
          case force book fT of
            All fA fB -> do
              check d span book ctx x fA
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
      infer d l book ctx t
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
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      inferOp2Type d span book ctx op a b ta tb
    Op1 op a -> do
      ta <- infer d span book ctx a
      inferOp1Type d span book ctx op a ta
    Pri U64_TO_CHAR -> do
      Done (All (Num U64_T) (Lam "x" (\_ -> Num CHR_T)))
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Check if a term has the expected type
check :: Int -> Span -> Book -> Context -> Term -> Term -> Result ()
check d span book ctx term goal =
  -- trace ("- check: " ++ show (normal 1 d book term) ++ " :: " ++ show (normal 1 d book goal)) $
  case (term, force book goal) of
    (Let v f, _) -> do
      case v of
        Chk val typ -> do
          check d span book ctx val typ
          check d span book ctx (App f (Ann val typ)) goal
        _ -> do
          t <- infer d span book ctx v
          check d span book ctx (App f (Ann v t)) goal
    (One, Uni) -> do
      Done ()
    (Bt0, Bit) -> do
      Done ()
    (Bt1, Bit) -> do
      Done ()
    (Zer, Nat) -> do
      Done ()
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      check d span book ctx n (Eql t a b)
    (Suc n, Nat) -> do
      check d span book ctx n Nat
    (Nil, Lst _) -> do
      Done ()
    (Nil, goal_ty) ->
      Fail $ TypeMismatch span (ctx term) (Lst (Var "_" 0)) goal_ty
    (Con h t, Lst tT) -> do
      check d span book ctx h tT
      check d span book ctx t (Lst tT)
    -- FIXME: doesn't work if we use 'All a b' because whnf removes the Ann (same for Sig)
    (Lam k f, All a (Lam _ b)) -> do
      let x = Ann (Var k d) a
      check (d+1) span book (extend d book ctx k a (Var k d)) (f x) (b x)
    (Efq, All a _) -> do
      case force book a of
        Emp -> Done ()
        _ -> Fail $ TypeMismatch span (ctx term) Emp a
    (Use f, All a b) -> do
      case force book a of
        Uni -> check d span book ctx f (App b One)
        _ -> Fail $ TypeMismatch span (ctx term) Uni a
    (Bif o i, All a b) -> do
      case force book a of
        Bit -> do
          check d span book ctx o (App b Bt0)
          check d span book ctx i (App b Bt1)
        _ -> Fail $ TypeMismatch span (ctx term) Bit a
    (Swi z s, All a b) -> do
      case force book a of
        Nat -> do
          check d span book ctx z (App b Zer)
          check d span book ctx s (All Nat (Lam "n" (\n -> App b (Suc n))))
        _ -> Fail $ TypeMismatch span (ctx term) Nat a
    (Mat n c, All a b) -> do
      case force book a of
        Lst _T -> do
          check d span book ctx n (App b Nil)
          check d span book ctx c (All _T (Lam "h" (\h -> All (Lst _T) (Lam "t" (\t -> App b (Con h t))))))
        _ -> Fail $ TypeMismatch span (ctx term) (Lst (Var "_" 0)) a
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch span (ctx term) (Enu y) (Sym s)
    (Cse c, All a b) -> do
      case force book a of
        Enu y -> do
          let s = map fst c
          if length s == length y && all (`elem` y) s
            then mapM_ (\(sym, term) -> check d span book ctx term (App b (Sym sym))) c >> Done ()
            else Fail $ TypeMismatch span (ctx term) (Enu y) (Enu s)
        _ -> Fail $ TypeMismatch span (ctx term) (Enu []) a
    (Get f, All a b) -> do
      case force book a of
        Sig x y -> check d span book ctx f (All x (Lam "x'" (\x' -> All (App y x') (Lam "y'" (\y' -> App b (Tup x' y'))))))
        _ -> Fail $ TypeMismatch span (ctx term) (Sig (Var "_" 0) (Lam "_" (\_ -> Var "_" 0))) a
    (Tup a b, Sig aT (Lam _ bT)) -> do
      check d span book ctx a aT
      check d span book ctx b (bT a)
    (Rfl, Eql t a b) -> do
      check d span book ctx a t
      check d span book ctx b t
      if equal d book a b
        then Done ()
        else Fail $ TermMismatch span (ctx term) (normal 1 d book a) (normal 1 d book b)
    (Rwt f, All a b) -> do
      case force book a of
        Eql t x y -> do
          let old = App b Rfl
          let neo = rewrite d book x y old
          check d span book ctx f neo
          -- trace ("rwt " ++ show x ++ " → " ++ show y ++ "\n- " ++ show old ++ "\n- " ++ show neo) $ check d span book ctx f neo
        _ -> Fail $ TypeMismatch span (ctx term) (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0)) (normal 1 d book a)
    (Fix k f, _) -> do
      check d span book (extend d book ctx k goal (Var k d)) (f (Ann (Fix k f) goal)) goal

    -- (App f (Ann v t), _) ->
      -- check d span book ctx f (All t $ Lam "_" $ \x -> rewrite d book v x goal)
    -- (App f x, goal) -> do
      -- xT <- infer d span book ctx x
      -- check d span book ctx (App f (Ann x xT)) goal

    -- Specializes pattern-matches:
    -- (λ{...} <x:X>) :: T
    -- ------------------------------------
    -- λ{...} :: ∀v:X.(rewrite x by v in T)
    (App f x, _) ->
      if isLamApp f
        then do
          (xv,xt) <- case strip x of
            Ann xv xt -> do
              return (xv, xt)
            xv -> do
              xt <- infer d span book ctx xv
              return (xv, xt)
          let ft = All xt $ Lam "_" $ \x -> rewrite d book xv x (whnf 1 book goal)
          check d span book ctx f ft
        else do
          verify d span book ctx term goal

    (Loc l t, _) -> do
      check d l book ctx t goal
    (Val (U64_V _), Num U64_T) -> do
      Done ()
    (Val (I64_V _), Num I64_T) -> do
      Done ()
    (Val (F64_V _), Num F64_T) -> do
      Done ()
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      tr <- inferOp2Type d span book ctx op a b ta tb
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (ctx term) goal tr
    (Op1 op a, _) -> do
      ta <- infer d span book ctx a
      tr <- inferOp1Type d span book ctx op a ta
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (ctx term) goal tr
    (Pat _ _ _, _) -> do
      error "not-supported"
    (_, _) -> do
      verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Context -> Term -> Term -> Result ()
verify d span book ctx term goal = do
  t <- infer d span book ctx term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch span (ctx term) (normal 1 d book goal) (normal 1 d book t)

-- Utils
-- -----

isLamApp :: Term -> Bool
isLamApp (strip -> App f _) = isLamApp f
isLamApp (strip -> Lam _ _) = True
isLamApp (strip -> Efq)     = True
isLamApp (strip -> Use _)   = True
isLamApp (strip -> Bif _ _) = True
isLamApp (strip -> Swi _ _) = True
isLamApp (strip -> Mat _ _) = True
isLamApp (strip -> Cse _)   = True
isLamApp (strip -> Get _)   = True
isLamApp (strip -> Rwt _)   = True
isLamApp _                  = False

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Context -> NOp2 -> Term -> Term -> Term -> Term -> Result Term
inferOp2Type d span book ctx op a b ta tb = do
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
inferOp1Type :: Int -> Span -> Book -> Context -> NOp1 -> Term -> Term -> Result Term
inferOp1Type d span book ctx op a ta = case op of
  NOT -> case force book ta of
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (ctx (Op1 op a))  -- Bitwise NOT not supported for CHR
    _ -> Fail $ CantInfer span (ctx (Op1 op a))
  NEG -> case force book ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (ctx (Op1 op a))  -- Negation not supported for CHR
    _ -> Fail $ CantInfer span (ctx (Op1 op a))
