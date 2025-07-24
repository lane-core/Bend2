{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import qualified Data.Map as M
import Data.List (find)
import Data.Maybe (fromJust)

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
infer :: Int -> Span -> Book -> Ctx -> Term -> Result Term
infer d span book@(Book defs _) ctx term =
  trace ("- infer: " ++ show (normal book term)) $
  case term of
    Var _ i -> do
      let Ctx ks = ctx
      if i < length ks
        then let (_, _, typ) = ks !! i
             in Done typ
        else Fail $ CantInfer span (normalCtx book ctx)
    Ref k i -> do
      case getDefn book k of
        Just (_, _, typ) -> Done typ
        Nothing          -> Fail $ Undefined span (normalCtx book ctx) k
    Sub x -> do
      infer d span book ctx x
    Let k t v f -> case t of
      Just t  -> do
        check d span book ctx v t
        infer (d+1) span book (extend ctx k v t) (f v)
      Nothing -> do
        t <- infer d span book ctx v
        infer (d+1) span book (extend ctx k v t) (f v)
    Fix k f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Chk v t -> do
      check d span book ctx v t
      Done t
    Set -> do
      Done Set
    Emp -> do
      Done Set
    EmpM -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Uni -> do
      Done Set
    One -> do
      Done Uni
    UniM _ -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Bit -> do
      Done Set
    Bt0 -> do
      Done Bit
    Bt1 -> do
      Done Bit
    BitM _ _ -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Nat -> do
      Done Set
    Zer -> do
      Done Nat
    Suc n -> do
      nT <- infer d span book ctx n
      case force book nT of
        Nat ->
          Done $ Nat
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book Nat) (normal book nT)
    NatM _ _ -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Lst t -> do
      check d span book ctx t Set
      Done Set
    Nil -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Con h t -> do
      Fail $ CantInfer span (normalCtx book ctx)
    LstM _ _ -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Enu s -> do
      Done Set
    Sym s -> do
      let bookEnums = [ Enu tags | (k, (_, (Sig (Enu tags) _), Set)) <- M.toList defs ]
      case find isEnuWithTag bookEnums of
        Just t  -> Done t
        Nothing -> Fail $ CantInfer span (normalCtx book ctx)
        where
          isEnuWithTag (Enu tags) = s `elem` tags
          isEnuWithTag _ = False
    EnuM _ _ -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Sig a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      Done Set
    Tup a b -> do
      aT <- infer d span book ctx a
      bT <- infer d span book ctx b
      Done $ Sig aT (Lam "_" Nothing (\_ -> bT))
    SigM _ -> do
      Fail $ CantInfer span (normalCtx book ctx)
    All a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      Done Set
    Lam k t b -> case t of
      Just tk  -> do 
        let x = Var k d
        tb <- infer (d+1) span book (extend ctx k x tk) (b x)
        Done $ All tk (Lam k (Just tk) (\v -> tb))
      Nothing -> do
        Fail $ CantInfer span (normalCtx book ctx)
    App f x ->
      case f of
        Lam k t body -> do
          xT <- infer d span book ctx x
          infer (d+1) span book (extend ctx k x xT) (body x)
        _ -> do
          fT <- infer d span book ctx f
          case force book fT of
            All fA fB -> do
              check d span book ctx x fA
              Done $ App fB x
            _ -> do
              Fail $ TypeMismatch span (normalCtx book ctx) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (normal book fT)
    Eql t a b -> do
      check d span book ctx t Set
      check d span book ctx a t
      check d span book ctx b t
      Done Set
    Rfl -> do
      Fail $ CantInfer span (normalCtx book ctx)
    EqlM f -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Rwt e f -> trace "rwt" $ do
      eT <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          -- Rewrite a by b in the context and goal, then infer f
          let rewrittenCtx = rewriteCtx d book a b ctx
          infer d span book rewrittenCtx f
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
    Met _ _ _ -> do
      Fail $ CantInfer span (normalCtx book ctx)
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
      Done (All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))
    Pri CHAR_TO_U64 -> do
      Done (All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))
    Log s x -> do
      check d span book ctx s (Lst (Num CHR_T))
      infer d span book ctx x
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Ctx -> NOp2 -> Term -> Term -> Term -> Term -> Result Term
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
      (Num t1, Num t2) | t1 == t2 -> Done (Num t1)
      (Nat, Nat) -> Done Nat  -- Allow Nat arithmetic operations
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)
    
    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done Bit
      (Bit, Bit) -> Done Bit  -- Allow Bool comparison
      (Nat, Nat) -> Done Bit  -- Allow Nat comparison
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)
    
    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> Done (Num U64_T)
      (Num I64_T, Num I64_T) -> Done (Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)
    
    boolOrIntegerOp ta tb = case (force book ta, force book tb) of
      (Bit, Bit) -> Done Bit  -- Logical operations on booleans
      (Num U64_T, Num U64_T) -> Done (Num U64_T)  -- Bitwise operations on integers
      (Num I64_T, Num I64_T) -> Done (Num U64_T)
      (Num F64_T, Num F64_T) -> Done (Num U64_T)
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Ctx -> NOp1 -> Term -> Term -> Result Term
inferOp1Type d span book ctx op a ta = case op of
  NOT -> case force book ta of
    Bit       -> Done Bit  -- Logical NOT on Bool
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)
  NEG -> case force book ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)

-- Check if a term has the expected type
check :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result ()
check d span book ctx (Loc l t) goal = check d l book ctx t goal 
check d span book ctx term      goal =
  trace ("- check: " ++ show term ++ " :: " ++ show (force book (normal book goal))) $
  case (term, force book goal) of
    (Era, _) -> do
      Done ()
    (Let k t v f, _) -> case t of
        Just t  -> do
          check d span book ctx v t
          check (d+1) span book (extend ctx k v t) (f v) goal
        Nothing -> do
          t <- infer d span book ctx v
          check (d+1) span book (extend ctx k v t) (f v) goal
    (One, Uni) -> do
      Done ()
    (Bt0, Bit) -> do
      Done ()
    (Bt1, Bit) -> do
      Done ()
    (Zer, Nat) -> do
      Done ()
    (Suc n, Nat) -> do
      check d span book ctx n Nat
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) ->
      check d span book ctx n (Eql t a b)
    (Nil, Lst _) -> do
      Done ()
    (Nil, goal) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book goal)
    (Con h t, Lst tT) -> do
      check d span book ctx h tT
      check d span book ctx t (Lst tT)
    (Lam k t f, All a b) -> do
      let x = Var k d
      check (d+1) span book (extend ctx k x a) (f x) (App b x)
    (EmpM, All (force book -> Eql t (force book -> Zer) (force book -> Suc y)) rT) -> do
      Done ()
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Zer)) rT) -> do
      Done ()
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Suc y)) rT) -> do
      check d span book ctx EmpM (All (Eql t x y) rT)
    (EmpM, All (force book -> Emp) rT) -> do
      Done ()
    (EmpM, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Emp (Lam "_" Nothing (\_ -> Set))))
    -- OTT allows typing Eql ↓
    -- (UniM f, All (force book -> Eql t a b) rT) -> do
      -- check d span book ctx a t
      -- check d span book ctx b t
      -- check d span book ctx f (App rT One)
    (UniM f, All (force book -> Uni) rT) -> do
      check d span book ctx f (App rT One)
      Done ()
    (UniM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Uni (Lam "_" Nothing (\_ -> Set))))
    (BitM f t, All (force book -> Bit) rT) -> do
      check d span book ctx f (App rT Bt0)
      check d span book ctx t (App rT Bt1)
      Done ()
    (BitM f t, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Bit (Lam "_" Nothing (\_ -> Set))))
    (NatM z s, All (force book -> Nat) rT) -> do
      check d span book ctx z (App rT Zer)
      check d span book ctx s (All Nat (Lam "p" Nothing (\p -> App rT (Suc p))))
      Done ()
    (NatM z s, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Nat (Lam "_" Nothing (\_ -> Set))))
    (LstM n c, All (force book -> Lst a) rT) -> do
      check d span book ctx n (App rT Nil)
      check d span book ctx c $ All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (\t -> App rT (Con h t)))))
      Done ()
    (LstM n c, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Lst (Var "_" 0)) (Lam "_" Nothing (\_ -> Set))))
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Enu y)) (normal book (Sym s))
    (EnuM cs df, All (force book -> Enu syms) rT) -> do
      mapM_ (\(s, t) -> check d span book ctx t (App rT (Sym s))) cs
      let covered_syms = map fst cs
      let all_covered = length covered_syms >= length syms
                     && all (`elem` syms) covered_syms
      if not all_covered
        then do
          case df of
            (cut -> Lam k Nothing (unlam k d -> One)) -> do
              Fail $ IncompleteMatch span (normalCtx book ctx)
            otherwise -> do
              let enu_type = Enu syms
              let lam_goal = All enu_type (Lam "_" Nothing (\v -> App rT v))
              check d span book ctx df lam_goal
        else Done ()
    (EnuM cs df, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu []) (Lam "_" Nothing (\_ -> Set))))
    (SigM f, All (force book -> Sig a b) rT) -> do
      check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (\t -> App rT (Tup h t)))))
      Done ()
    (SigM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> Set))))
    (Tup a b, Sig aT bT) -> do
      check d span book ctx a aT
      check d span book ctx b (App bT a)
    (Rfl, Eql t a b) -> do
      -- Check that a and b are equal for reflexivity
      if equal d book a b
        then Done ()
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book a) (normal book b)
    (EqlM f, All (force book -> Eql t a b) rT) -> do
      -- When matching on {==}, we rewrite the goal and context
      -- replacing all occurrences of a with b
      let rewrittenGoal = rewrite d book a b (App rT Rfl)
      let rewrittenCtx = rewriteCtx d book a b ctx
      check d span book rewrittenCtx f rewrittenGoal
    (Fix k f, _) -> do
      check (d+1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal
    (Val (U64_V _), Num U64_T) -> do
      Done ()
    (Val (I64_V _), Num I64_T) -> do
      Done ()
    (Val (F64_V _), Num F64_T) -> do
      Done ()
    (Val (CHR_V _), Num CHR_T) -> do
      Done ()
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      tr <- inferOp2Type d span book ctx op a b ta tb
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)
    (Op1 op a, _) -> do
      ta <- infer d span book ctx a
      tr <- inferOp1Type d span book ctx op a ta
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)
    (Sup l a b, _) -> do
      check d span book ctx a goal
      check d span book ctx b goal
    (SupM l f, _) -> do
      check d span book ctx l (Num U64_T)
      case force book goal of
        All xT rT -> do
          check d span book ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (\q -> App rT (Sup l p q))))))
          Done ()
        _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Set))))
    (Frk l a b, _) -> do
      check d span book ctx l (Num U64_T)
      check d span book ctx a goal
      check d span book ctx b goal
    (Rwt e f, _) -> trace "rwt" $ do
      eT <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          -- Rewrite a by b in the context and goal
          let rewrittenCtx = rewriteCtx d book a b ctx
          let rewrittenGoal = rewrite d book a b goal
          check d span book rewrittenCtx f rewrittenGoal
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT)
    (Pat _ _ _, _) -> do
      error "not-supported"
    -- (App f x, _) -> do
      -- trace ("- check App: " ++ show (App f x) ++ " :: " ++ show goal) $ do
        -- verify d span book ctx term goal
    (Log s x, _) -> do
      check d span book ctx s (Lst (Num CHR_T))
      check d span book ctx x goal
    (Lam f t x, _) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1)
    -- FIXME: implement a proper refl?
    -- (x, Eql t a b) | equal d book a b && equal d book a x -> do
      -- Done ()
      -- checks if x == a and x == b
      -- if equal d book x a && equal d book x b
        -- then Done ()
        -- else Fail $ TermMismatch span (normalCtx book ctx) (normal book x) (Eql t (normal book a) (normal book b))
    (_, _) -> do
      verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result ()
verify d span book ctx term goal = do
  t <- infer d span book ctx term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t)

-- Utils
-- -----

-- Check all definitions in a Book
checkBook :: Book -> Result ()
checkBook book@(Book defs names) = mapM_ checkDef [(name, fromJust (M.lookup name defs)) | name <- names]
  where
    checkDef (name, (_, term, typ)) = do
      trace ("CHECKING DEF: " ++ name) $ do
        check 0 noSpan book (Ctx []) term typ

