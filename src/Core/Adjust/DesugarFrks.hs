{-# LANGUAGE ViewPatterns #-}

-- Fork Desugaring
-- ===============
-- Removes all Frks from a Term, as follows:
--   fork L: A else: B (with ctx=[a,b,...])
--   --------------------------------------
--   &L{a0,a1} = a
--   &L{b0,b1} = b
--   ...
--   &L{A[a<-a0, b<-b0, ...], B[a<-a1,b<-b1, ...]}
-- That is, whenever a 'Frk L a b' constructor is found, we:
-- 1. Superpose each variable of the context (using a SupM with label L)
-- 2. Return a Sup of a and b, where the context on each side is entirely
--    replaced by the corresponding side of the forked variable

module Core.Adjust.DesugarFrks where

import Core.Bind
import Core.FreeVars
import Core.Show
import Core.Type
import qualified Data.Set as S

desugarFrks :: Int -> Term -> Term
desugarFrks d term = desugarFrksGo d [] term

desugarFrksGo :: Int -> [(Name, Int)] -> Term -> Term
desugarFrksGo d ctx (Var n i)     = Var n i
desugarFrksGo d ctx (Ref n i)     = Ref n i
desugarFrksGo d ctx (Sub t)       = Sub (desugarFrksGo d ctx t)
desugarFrksGo d ctx (Fix n f)     = Fix n (\x -> desugarFrksGo (d+1) ((n,d):ctx) (f x))
desugarFrksGo d ctx (Let k t v f) = Let k (fmap (desugarFrksGo d ctx) t) (desugarFrksGo d ctx v) (\x -> desugarFrksGo (d+1) ((k,d):ctx) (f x))
desugarFrksGo d ctx (Use k v f)   = Use k (desugarFrksGo d ctx v) (\x -> desugarFrksGo (d+1) ((k,d):ctx) (f x))
desugarFrksGo d ctx Set           = Set
desugarFrksGo d ctx (Chk x t)     = Chk (desugarFrksGo d ctx x) (desugarFrksGo d ctx t)
desugarFrksGo d ctx Emp           = Emp
desugarFrksGo d ctx EmpM          = EmpM
desugarFrksGo d ctx Uni           = Uni
desugarFrksGo d ctx One           = One
desugarFrksGo d ctx (UniM f)      = UniM (desugarFrksGo d ctx f)
desugarFrksGo d ctx Bit           = Bit
desugarFrksGo d ctx Bt0           = Bt0
desugarFrksGo d ctx Bt1           = Bt1
desugarFrksGo d ctx (BitM f t)    = BitM (desugarFrksGo d ctx f) (desugarFrksGo d ctx t)
desugarFrksGo d ctx Nat           = Nat
desugarFrksGo d ctx Zer           = Zer
desugarFrksGo d ctx (Suc n)       = Suc (desugarFrksGo d ctx n)
desugarFrksGo d ctx (NatM z s)    = NatM (desugarFrksGo d ctx z) (desugarFrksGo d ctx s)
desugarFrksGo d ctx (Lst t)       = Lst (desugarFrksGo d ctx t)
desugarFrksGo d ctx Nil           = Nil
desugarFrksGo d ctx (Con h t)     = Con (desugarFrksGo d ctx h) (desugarFrksGo d ctx t)
desugarFrksGo d ctx (LstM n c)    = LstM (desugarFrksGo d ctx n) (desugarFrksGo d ctx c)
desugarFrksGo d ctx (Enu s)       = Enu s
desugarFrksGo d ctx (Sym s)       = Sym s
desugarFrksGo d ctx (EnuM c e)    = EnuM [(s, desugarFrksGo d ctx t) | (s, t) <- c] (desugarFrksGo d ctx e)
desugarFrksGo d ctx (Sig a b)     = Sig (desugarFrksGo d ctx a) (desugarFrksGo d ctx b)
desugarFrksGo d ctx (Tup a b)     = Tup (desugarFrksGo d ctx a) (desugarFrksGo d ctx b)
desugarFrksGo d ctx (SigM f)      = SigM (desugarFrksGo d ctx f)
desugarFrksGo d ctx (All a b)     = All (desugarFrksGo d ctx a) (desugarFrksGo d ctx b)
desugarFrksGo d ctx (Lam n t f)   = Lam n (fmap (desugarFrksGo d ctx) t) (\x -> desugarFrksGo (d+1) ((n,d):ctx) (f x))
desugarFrksGo d ctx (App f x)     = App (desugarFrksGo d ctx f) (desugarFrksGo d ctx x)
desugarFrksGo d ctx (Eql t a b)   = Eql (desugarFrksGo d ctx t) (desugarFrksGo d ctx a) (desugarFrksGo d ctx b)
desugarFrksGo d ctx Rfl           = Rfl
desugarFrksGo d ctx (EqlM f)      = EqlM (desugarFrksGo d ctx f)
desugarFrksGo d ctx (Met i t x)   = Met i (desugarFrksGo d ctx t) (map (desugarFrksGo d ctx) x)
desugarFrksGo d ctx Era           = Era
desugarFrksGo d ctx (Sup l a b)   = Sup (desugarFrksGo d ctx l) (desugarFrksGo d ctx a) (desugarFrksGo d ctx b)
desugarFrksGo d ctx (SupM l f)    = SupM (desugarFrksGo d ctx l) (desugarFrksGo d ctx f)
desugarFrksGo d ctx (Frk l a b)   = desugarFrk d ctx l a b
desugarFrksGo d ctx (Rwt e f)     = Rwt (desugarFrksGo d ctx e) (desugarFrksGo d ctx f)
desugarFrksGo d ctx (Num t)       = Num t
desugarFrksGo d ctx (Val v)       = Val v
desugarFrksGo d ctx (Op2 o a b)   = Op2 o (desugarFrksGo d ctx a) (desugarFrksGo d ctx b)
desugarFrksGo d ctx (Op1 o a)     = Op1 o (desugarFrksGo d ctx a)
desugarFrksGo d ctx (Pri p)       = Pri p
desugarFrksGo d ctx (Log s x)     = Log (desugarFrksGo d ctx s) (desugarFrksGo d ctx x)
desugarFrksGo d ctx (Loc s t)     = Loc s (desugarFrksGo d ctx t)
desugarFrksGo d ctx (Pat s m c)   = Pat (map (desugarFrksGo d ctx) s) [(k, desugarFrksGo d ctx v) | (k,v) <- m] [(p, desugarFrksGo d (ctxCs p) f) | (p, f) <- c]
  where ctxCs  p = ctx ++ map (\(k,v) -> (k, d)) m ++ ctxPat p
        ctxPat p = map (\k -> (k, d)) (S.toList (S.unions (map (freeVars S.empty) p)))

desugarFrk :: Int -> [(Name, Int)] -> Term -> Term -> Term -> Term
desugarFrk d ctx l a b = buildSupMs vars where
  vars =  shadowCtx (filter (\x -> fst x `S.member` free) (reverse ctx))
  free = case cut l of
    -- 'l' must be a non-superposed U64 so we can remove it from the forked vars as a (reasonable) optimization.
    Var n _ -> S.delete n (freeVars S.empty a `S.union` freeVars S.empty b)
    _       -> freeVars S.empty a `S.union` freeVars S.empty b
  -- Build nested SupM matches for each context variable
  buildSupMs :: [(Name, Int)] -> Term
  buildSupMs [] = Sup l a' b' where
    ls = [(n, Var (n++"0") 0) | (n, _) <- vars]
    rs = [(n, Var (n++"1") 0) | (n, _) <- vars]
    a' = bindNameMany ls (desugarFrksGo d ctx a)
    b' = bindNameMany rs (desugarFrksGo d ctx b)
  -- For each variable, create a SupM that binds the superposed versions
  buildSupMs ((n,d):rest) =
    App (SupM l $
    Lam (n++"0") Nothing $ \_ ->
    Lam (n++"1") Nothing $ \_ ->
    buildSupMs rest) (Var n d)
  -- Removes repeated (shadowed) vars from the context
  shadowCtx ((n,d):ctx) =
    if n `elem` (map fst ctx)
      then shadowCtx ctx
      else (n,d) : shadowCtx ctx
  shadowCtx [] = []
