{-./Type.hs-}

module Core.Bind where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Debug.Trace

import Core.Type
import Core.FreeVars

bind :: Term -> Term
bind term = bound where
  bound = binder 0 term [] M.empty

binder :: Int -> Term -> [Term] -> M.Map Name Term -> Term
binder lv term ctx vars = case term of
  Var k i     -> case M.lookup k vars of { Just t -> t ; Nothing -> Ref k 1}
  Ref k i     -> Ref k i
  Sub t       -> t
  Let k t v f -> Let k (fmap (\u -> binder lv u ctx vars) t) (binder lv v ctx vars) (\x -> binder lv (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Use k v f   -> Use k (binder lv v ctx vars) (\x -> binder lv (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Fix k f     -> Fix k (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Set         -> Set
  Chk x t     -> Chk (binder lv x ctx vars) (binder lv t ctx vars)
  Emp         -> Emp
  EmpM        -> EmpM
  Uni         -> Uni
  One         -> One
  UniM f      -> UniM (binder lv f ctx vars)
  Bit         -> Bit
  Bt0         -> Bt0
  Bt1         -> Bt1
  BitM f t    -> BitM (binder lv f ctx vars) (binder lv t ctx vars)
  Nat         -> Nat
  Zer         -> Zer
  Suc n       -> Suc (binder lv n ctx vars)
  NatM z s    -> NatM (binder lv z ctx vars) (binder lv s ctx vars)
  Lst t       -> Lst (binder lv t ctx vars)
  Nil         -> Nil
  Con h t     -> Con (binder lv h ctx vars) (binder lv t ctx vars)
  LstM n c    -> LstM (binder lv n ctx vars) (binder lv c ctx vars)
  Enu s       -> Enu s
  Sym s       -> Sym s
  EnuM c e    -> EnuM (map (\(s, t) -> (s, binder lv t ctx vars)) c) (binder lv e ctx vars)
  Sig a b     -> Sig (binder lv a ctx vars) (binder lv b ctx vars)
  Tup a b     -> Tup (binder lv a ctx vars) (binder lv b ctx vars)
  SigM f      -> SigM (binder lv f ctx vars)
  All a b     -> All (binder lv a ctx vars) (binder lv b ctx vars)
  Lam k t f   -> Lam k (fmap (\t -> binder lv t ctx vars) t) (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  App f x     -> App (binder lv f ctx vars) (binder lv x ctx vars)
  Eql t a b   -> Eql (binder lv t ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  Rfl         -> Rfl
  EqlM f      -> EqlM (binder lv f ctx vars)
  Rwt e f     -> Rwt (binder lv e ctx vars) (binder lv f ctx vars)
  Loc s t     -> Loc s (binder lv t ctx vars)
  Era         -> Era
  Sup l a b   -> Sup (binder lv l ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  SupM l f    -> SupM (binder lv l ctx vars) (binder lv f ctx vars)
  Frk l a b   -> Frk (binder lv l ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  Num t       -> Num t
  Val v       -> Val v
  Op2 o a b   -> Op2 o (binder lv a ctx vars) (binder lv b ctx vars)
  Op1 o a     -> Op1 o (binder lv a ctx vars)
  Pri p       -> Pri p
  Log s x     -> Log (binder lv s ctx vars) (binder lv x ctx vars)
  Met k t c   -> Met k (binder lv t ctx vars) (map (\x -> binder lv x ctx vars) c)
  Pat s m c   -> undefined

    -- -- Since Pat doesn't bind with HOAS, keep as Var
    -- let s'     = map (\x -> binder lv x ctx vars) s
        -- m'     = map (\(k,x) -> (k, binder lv x ctx vars)) m
        -- c'     = map (\(p,x) -> (p, binder lv x (ctx ++ map v mvar ++ map v (pvar p)) (M.union (M.fromList (map kv (mvar ++ pvar p))) vars))) c
        -- mvar   = map fst m
        -- pvar p = S.toList (S.unions (map (freeVars S.empty) p))
        -- kv nam = (nam, Var nam 0)
        -- v nam  = Var nam 0
    -- in Pat s' m' c'

-- Binds a single variable
bindVar :: Int -> Term -> Term -> Term
bindVar i x (Var k i')
  | i == i'   = x
  | otherwise = Var k i'
bindVar i x (Ref k j)      = Ref k j
bindVar i x (Sub t)        = t
bindVar i x (Fix k f)      = Fix k (\v -> bindVar i x (f (Sub v)))
bindVar i x (Let k t v f)  = Let k (fmap (bindVar i x) t) (bindVar i x v) (\v -> bindVar i x (f (Sub v)))
bindVar i x (Use k v f)    = Use k (bindVar i x v) (\v -> bindVar i x (f (Sub v)))
bindVar i x Set            = Set
bindVar i x (Chk v t)      = Chk (bindVar i x v) (bindVar i x t)
bindVar i x Emp            = Emp
bindVar i x EmpM           = EmpM
bindVar i x Uni            = Uni
bindVar i x One            = One
bindVar i x (UniM f)       = UniM (bindVar i x f)
bindVar i x Bit            = Bit
bindVar i x Bt0            = Bt0
bindVar i x Bt1            = Bt1
bindVar i x (BitM f t)     = BitM (bindVar i x f) (bindVar i x t)
bindVar i x Nat            = Nat
bindVar i x Zer            = Zer
bindVar i x (Suc n)        = Suc (bindVar i x n)
bindVar i x (NatM z s)     = NatM (bindVar i x z) (bindVar i x s)
bindVar i x (Lst t)        = Lst (bindVar i x t)
bindVar i x Nil            = Nil
bindVar i x (Con h t)      = Con (bindVar i x h) (bindVar i x t)
bindVar i x (LstM n c)     = LstM (bindVar i x n) (bindVar i x c)
bindVar i x (Enu ss)       = Enu ss
bindVar i x (Sym s)        = Sym s
bindVar i x (EnuM cs e)    = EnuM (map (\(s,t) -> (s, bindVar i x t)) cs) (bindVar i x e)
bindVar i x (Num t)        = Num t
bindVar i x (Val v)        = Val v
bindVar i x (Op2 op a b)   = Op2 op (bindVar i x a) (bindVar i x b)
bindVar i x (Op1 op a)     = Op1 op (bindVar i x a)
bindVar i x (Sig a b)      = Sig (bindVar i x a) (bindVar i x b)
bindVar i x (Tup a b)      = Tup (bindVar i x a) (bindVar i x b)
bindVar i x (SigM f)       = SigM (bindVar i x f)
bindVar i x (All a b)      = All (bindVar i x a) (bindVar i x b)
bindVar i x (Lam k t f)    = Lam k (fmap (bindVar i x) t) (\v -> bindVar i x (f (Sub v)))
bindVar i x (App f a)      = App (bindVar i x f) (bindVar i x a)
bindVar i x (Eql t a b)    = Eql (bindVar i x t) (bindVar i x a) (bindVar i x b)
bindVar i x Rfl            = Rfl
bindVar i x (EqlM f)       = EqlM (bindVar i x f)
bindVar i x (Rwt e f)      = Rwt (bindVar i x e) (bindVar i x f)
bindVar i x (Met n t ctx)  = Met n (bindVar i x t) (map (bindVar i x) ctx)
bindVar i x Era            = Era
bindVar i x (Sup l a b)    = Sup (bindVar i x l) (bindVar i x a) (bindVar i x b)
bindVar i x (SupM l f)     = SupM (bindVar i x l) (bindVar i x f)
bindVar i x (Frk l a b)    = Frk (bindVar i x l) (bindVar i x a) (bindVar i x b)
bindVar i x (Loc s t)      = Loc s (bindVar i x t)
bindVar i x (Log s t)      = Log (bindVar i x s) (bindVar i x t)
bindVar i x (Pri p)        = Pri p
bindVar i x (Pat ts ms cs) = Pat (map (bindVar i x) ts) (map (\(k,v) -> (k, bindVar i x v)) ms) (map (\(ps,b) -> (map (bindVar i x) ps, bindVar i x b)) cs)


