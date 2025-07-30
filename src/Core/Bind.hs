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
  Pat s m c   -> error "unreachable"
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
bindIndex :: Int -> Term -> Term -> Term
bindIndex i x (Var k i')
  | i == i'   = x
  | otherwise = Var k i'
bindIndex i x (Ref k j)      = Ref k j
bindIndex i x (Sub t)        = t
bindIndex i x (Fix k f)      = Fix k (\v -> bindIndex i x (f (Sub v)))
bindIndex i x (Let k t v f)  = Let k (fmap (bindIndex i x) t) (bindIndex i x v) (\v -> bindIndex i x (f (Sub v)))
bindIndex i x (Use k v f)    = Use k (bindIndex i x v) (\v -> bindIndex i x (f (Sub v)))
bindIndex i x Set            = Set
bindIndex i x (Chk v t)      = Chk (bindIndex i x v) (bindIndex i x t)
bindIndex i x Emp            = Emp
bindIndex i x EmpM           = EmpM
bindIndex i x Uni            = Uni
bindIndex i x One            = One
bindIndex i x (UniM f)       = UniM (bindIndex i x f)
bindIndex i x Bit            = Bit
bindIndex i x Bt0            = Bt0
bindIndex i x Bt1            = Bt1
bindIndex i x (BitM f t)     = BitM (bindIndex i x f) (bindIndex i x t)
bindIndex i x Nat            = Nat
bindIndex i x Zer            = Zer
bindIndex i x (Suc n)        = Suc (bindIndex i x n)
bindIndex i x (NatM z s)     = NatM (bindIndex i x z) (bindIndex i x s)
bindIndex i x (Lst t)        = Lst (bindIndex i x t)
bindIndex i x Nil            = Nil
bindIndex i x (Con h t)      = Con (bindIndex i x h) (bindIndex i x t)
bindIndex i x (LstM n c)     = LstM (bindIndex i x n) (bindIndex i x c)
bindIndex i x (Enu ss)       = Enu ss
bindIndex i x (Sym s)        = Sym s
bindIndex i x (EnuM cs e)    = EnuM (map (\(s,t) -> (s, bindIndex i x t)) cs) (bindIndex i x e)
bindIndex i x (Num t)        = Num t
bindIndex i x (Val v)        = Val v
bindIndex i x (Op2 op a b)   = Op2 op (bindIndex i x a) (bindIndex i x b)
bindIndex i x (Op1 op a)     = Op1 op (bindIndex i x a)
bindIndex i x (Sig a b)      = Sig (bindIndex i x a) (bindIndex i x b)
bindIndex i x (Tup a b)      = Tup (bindIndex i x a) (bindIndex i x b)
bindIndex i x (SigM f)       = SigM (bindIndex i x f)
bindIndex i x (All a b)      = All (bindIndex i x a) (bindIndex i x b)
bindIndex i x (Lam k t f)    = Lam k (fmap (bindIndex i x) t) (\v -> bindIndex i x (f (Sub v)))
bindIndex i x (App f a)      = App (bindIndex i x f) (bindIndex i x a)
bindIndex i x (Eql t a b)    = Eql (bindIndex i x t) (bindIndex i x a) (bindIndex i x b)
bindIndex i x Rfl            = Rfl
bindIndex i x (EqlM f)       = EqlM (bindIndex i x f)
bindIndex i x (Rwt e f)      = Rwt (bindIndex i x e) (bindIndex i x f)
bindIndex i x (Met n t ctx)  = Met n (bindIndex i x t) (map (bindIndex i x) ctx)
bindIndex i x Era            = Era
bindIndex i x (Sup l a b)    = Sup (bindIndex i x l) (bindIndex i x a) (bindIndex i x b)
bindIndex i x (SupM l f)     = SupM (bindIndex i x l) (bindIndex i x f)
bindIndex i x (Frk l a b)    = Frk (bindIndex i x l) (bindIndex i x a) (bindIndex i x b)
bindIndex i x (Loc s t)      = Loc s (bindIndex i x t)
bindIndex i x (Log s t)      = Log (bindIndex i x s) (bindIndex i x t)
bindIndex i x (Pri p)        = Pri p
bindIndex i x (Pat ts ms cs) = Pat (map (bindIndex i x) ts) (map (\(k,v) -> (k, bindIndex i x v)) ms) (map (\(ps,b) -> (map (bindIndex i x) ps, bindIndex i x b)) cs)

-- Subst a var for a value in a term
bindName :: Name -> Term -> Term -> Term
bindName name val term = go name val term where
  go name val term = case term of
    Var k _     -> if k == name then val else term
    Ref k i     -> Ref k i
    Sub t       -> Sub (go name val t)
    Fix k f     -> if k == name then term else Fix k (\x -> go name val (f x))
    Let k t v f -> if k == name then term else Let k (fmap (go name val) t) (go name val v) (\x -> go name val (f x))
    Use k v f   -> if k == name then term else Use k (go name val v) (\x -> go name val (f x))
    Chk x t     -> Chk (go name val x) (go name val t)
    Set         -> Set
    Emp         -> Emp
    EmpM        -> EmpM
    Uni         -> Uni
    One         -> One
    UniM f      -> UniM (go name val f)
    Bit         -> Bit
    Bt0         -> Bt0
    Bt1         -> Bt1
    BitM f t    -> BitM (go name val f) (go name val t)
    Nat         -> Nat
    Zer         -> Zer
    Suc n       -> Suc (go name val n)
    NatM z s    -> NatM (go name val z) (go name val s)
    Lst t       -> Lst (go name val t)
    Nil         -> Nil
    Con h t     -> Con (go name val h) (go name val t)
    LstM n c    -> LstM (go name val n) (go name val c)
    Enu s       -> Enu s
    Sym s       -> Sym s
    EnuM c e    -> EnuM [(s, go name val t) | (s, t) <- c] (go name val e)
    Sig a b     -> Sig (go name val a) (go name val b)
    Tup a b     -> Tup (go name val a) (go name val b)
    SigM f      -> SigM (go name val f)
    All a b     -> All (go name val a) (go name val b)
    Lam k t f   -> if k == name then term else Lam k (fmap (go name val) t) (\x -> go name val (f x))
    App f x     -> App (go name val f) (go name val x)
    Eql t a b   -> Eql (go name val t) (go name val a) (go name val b)
    Rfl         -> Rfl
    EqlM f      -> EqlM (go name val f)
    Met i t x   -> Met i (go name val t) (map (go name val) x)
    Era         -> Era
    Sup l a b   -> Sup (go name val l) (go name val a) (go name val b)
    SupM l f    -> SupM (go name val l) (go name val f)
    Frk l a b   -> Frk (go name val l) (go name val a) (go name val b)
    Rwt e f     -> Rwt (go name val e) (go name val f)
    Num t       -> Num t
    Val v       -> Val v
    Op2 o a b   -> Op2 o (go name val a) (go name val b)
    Op1 o a     -> Op1 o (go name val a)
    Pri p       -> Pri p
    Log s x     -> Log (go name val s) (go name val x)
    Loc s t     -> Loc s (go name val t)
    Pat s m c   -> Pat (map (go name val) s) m (map cse c)
      where cse (pats, rhs) = (map (go name val) pats, go name val rhs)

-- Helper to substitute multiple variables at once
bindNameMany :: [(Name, Term)] -> Term -> Term
bindNameMany subs term = foldr (\ (n,v) t -> bindName n v t) term subs
