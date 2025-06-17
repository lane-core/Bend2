{-./Type.hs-}
{-./WHNF.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import Debug.Trace
import qualified Data.Map as M

import Core.Equal
import Core.Normal
import Core.Rewrite
import Core.Type
import Core.WHNF

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
checkBook :: Int -> Book -> Result ()
checkBook d book@(Book defs) = mapM_ checkDefn (M.toList defs)
  where checkDefn (name, (term, typ)) = check d book id term typ

-- Infer the type of a term
infer :: Int -> Book -> Context -> Term -> Result Term
infer d book ctx term =
  -- trace ("- infer: " ++ show term) $
  case term of
    Var k i -> do
      Fail $ CantInfer (ctx term)
    Ref k -> do
      case deref book k of
        Just (_, typ) -> Done typ
        Nothing -> Fail $ CantInfer (ctx term)
    Sub x -> do
      infer d book ctx x
    Let v f -> do
      case v of
        Chk val typ -> do
          check d book ctx val typ
          infer d book ctx (App f (Ann val typ))
        _ -> do
          t <- infer d book ctx v
          infer d book ctx (App f (Ann v t))
    Fix k f -> do
      Fail $ CantInfer (ctx term)
    Ann v t -> do
      Done t
    Chk v t -> do
      check d book ctx v t
      Done t
    Set -> do
      Done Set
    Emp -> do
      Done Set
    Efq -> do
      Fail $ CantInfer (ctx term)
    Uni -> do
      Done Set
    One -> do
      Done Uni
    Use f -> do
      Fail $ CantInfer (ctx term)
    Bit -> do
      Done Set
    Bt0 -> do
      Done Bit
    Bt1 -> do
      Done Bit
    Bif o i -> do
      Fail $ CantInfer (ctx term)
    Nat -> do
      Done Set
    Zer -> do
      Done Nat
    Suc n -> do
      nT <- infer d book ctx n
      case force book nT of
        Nat ->
          Done $ Nat
        Eql Nat a b ->
          Done $ Eql Nat (Suc a) (Suc b)
        otherwise ->
          Fail $ TypeMismatch (ctx term) Nat (normal 1 d book nT)
    Swi z s -> do
      Fail $ CantInfer (ctx term)
    Lst t -> do
      check d book ctx t Set
      Done Set
    Nil -> do
      Fail $ CantInfer (ctx term)
    Con h t -> do
      Fail $ CantInfer (ctx term)
    Mat n c -> do
      Fail $ CantInfer (ctx term)
    Enu s -> do
      Done Set
    Sym s -> do
      Fail $ CantInfer (ctx term)
    Cse c -> do
      Fail $ CantInfer (ctx term)
    Sig a b -> do
      check d book ctx a Set
      check d book ctx b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Tup a b -> do
      aT <- infer d book ctx a
      bT <- infer d book ctx b
      Done $ Sig aT (Lam "_" (\_ -> bT))
    Get f -> do
      Fail $ CantInfer (ctx term)
    All a b -> do
      check d book ctx a Set
      check d book ctx b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Lam _ _ -> do
      Fail $ CantInfer (ctx term)
    App f x ->
      case (f,x) of
        -- TODO: can we generalize this to other lam forms?
        (Lam k f, Ann xv xt) -> do
          infer (d+1) book (extend d book ctx k xt xv) (f (Ann xv xt))
        _ -> do
          fT <- infer d book ctx f
          case force book fT of
            All fA fB -> do
              check d book ctx x fA
              Done $ App fB x
            _ -> do
              Fail $ TypeMismatch (ctx term) (All (Var "_" 0) (Lam "_" (\_ -> Var "_" 0))) fT
    Eql t a b -> do
      Done Set
    Rfl -> do
      Fail $ CantInfer (ctx term)
    Rwt f -> do
      Fail $ CantInfer (ctx term)
    Ind _ -> do
      Fail $ CantInfer (ctx term)
    Frz _ -> do
      Fail $ CantInfer (ctx term)
    Era -> do
      Fail $ CantInfer (ctx term)
    Sup l a b -> do
      Fail $ CantInfer (ctx term)
    Met _ _ _ -> do
      Fail $ CantInfer (ctx term)
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Check if a term has the expected type
check :: Int -> Book -> Context -> Term -> Term -> Result ()
check d book ctx term goal' =
  let goal = force book goal' in
  -- trace ("- check: " ++ show (term) ++ " :: " ++ show (goal)) $
  case (term, goal) of
    (Let v f, goal) -> do
      case v of
        Chk val typ -> do
          check d book ctx val typ
          check d book ctx (App f (Ann val typ)) goal
        _ -> do
          t <- infer d book ctx v
          check d book ctx (App f (Ann v t)) goal
    (One, Uni) -> do
      Done ()
    (Bt0, Bit) -> do
      Done ()
    (Bt1, Bit) -> do
      Done ()
    (Zer, Nat) -> do
      Done ()
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      check d book ctx n (Eql t a b)
    (Suc n, Nat) -> do
      check d book ctx n Nat
    (Nil, Lst _) -> do
      Done ()
    (Con h t, Lst tT) -> do
      check d book ctx h tT
      check d book ctx t (Lst tT)
    -- FIXME: doesn't work if we use 'All a b' because whnf removes the Ann (same for Sig)
    (Lam k f, All a (Lam _ b)) -> do
      let x = Ann (Var k d) a
      check (d+1) book (extend d book ctx k a (Var k d)) (f x) (b x)
    (Efq, All a _) -> do
      case force book a of
        Emp -> Done ()
        _ -> Fail $ TypeMismatch (ctx term) Emp a
    (Use f, All a b) -> do
      case force book a of
        Uni -> check d book ctx f (App b One)
        _ -> Fail $ TypeMismatch (ctx term) Uni a
    (Bif o i, All a b) -> do
      case force book a of
        Bit -> do
          check d book ctx o (App b Bt0)
          check d book ctx i (App b Bt1)
        _ -> Fail $ TypeMismatch (ctx term) Bit a
    (Swi z s, All a b) -> do
      case force book a of
        Nat -> do
          check d book ctx z (App b Zer)
          check d book ctx s (All Nat (Lam "n" (\n -> App b (Suc n))))
        _ -> Fail $ TypeMismatch (ctx term) Nat a
    (Mat n c, All a b) -> do
      case force book a of
        Lst _T -> do
          check d book ctx n (App b Nil)
          check d book ctx c (All _T (Lam "h" (\h -> All (Lst _T) (Lam "t" (\t -> App b (Con h t))))))
        _ -> Fail $ TypeMismatch (ctx term) (Lst (Var "_" 0)) a
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch (ctx term) (Enu y) (Sym s)
    (Cse c, All a b) -> do
      case force book a of
        Enu y -> do
          let s = map fst c
          if length s == length y && all (`elem` y) s
            then mapM_ (\(sym, term) -> check d book ctx term (App b (Sym sym))) c >> Done ()
            else Fail $ TypeMismatch (ctx term) (Enu y) (Enu s)
        _ -> Fail $ TypeMismatch (ctx term) (Enu []) a
    (Get f, All a b) -> do
      case force book a of
        Sig x y -> check d book ctx f (All x (Lam "x'" (\x' -> All (App y x') (Lam "y'" (\y' -> App b (Tup x' y'))))))
        _ -> Fail $ TypeMismatch (ctx term) (Sig (Var "_" 0) (Lam "_" (\_ -> Var "_" 0))) a
    (Tup a b, Sig aT (Lam _ bT)) -> do
      check d book ctx a aT
      check d book ctx b (bT a)
    (Rfl, Eql t a b) -> do
      check d book ctx a t
      check d book ctx b t
      if equal d book a b
        then Done ()
        else Fail $ TermMismatch (ctx term) (normal 1 d book a) (normal 1 d book b)
    (Rwt f, All a b) -> do
      case force book a of
        Eql t x y -> check d book ctx f (rewrite d book x y (App b Rfl))
        _ -> Fail $ TypeMismatch (ctx term) (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0)) (normal 1 d book a)
    (Fix k f, _) -> do
      check d book (extend d book ctx k goal (Var k d)) (f (Ann (Fix k f) goal)) goal
    (App f (Ann v t), goal) ->
      check d book ctx f (All t $ Lam "_" $ \x -> rewrite d book v x goal)
    (App f x, goal) -> do
      xT <- infer d book ctx x
      check d book ctx (App f (Ann x xT)) goal
    (Pat _ _ _, _) -> do
      error "not-supported"
    (_, _) -> do
      verify d book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Book -> Context -> Term -> Term -> Result ()
verify d book ctx term goal = do
  t <- infer d book ctx term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch (ctx term) (normal 1 d book goal) (normal 1 d book t)

