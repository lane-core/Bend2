
-- Normalization
-- =============

normal :: Int -> Int -> Book -> Term -> Term
normal lv d book term =
  -- trace ("normal: " ++ show lv ++ " " ++ show term) $
  case whnf lv d book term of
    Var k i    -> Var k i
    Ref k      -> Ref k
    Sub t      -> normal lv d book t
    Fix k f    -> Fix k (\x -> normal lv (d+1) book (f x))
    Let v f    -> Let (normal lv d book v) (normal lv d book f)
    Set        -> Set
    Ann x t    -> Ann (normal lv d book x) (normal lv d book t)
    Chk x t    -> Chk (normal lv d book x) (normal lv d book t)
    Emp        -> Emp
    Efq        -> Efq
    Uni        -> Uni
    One        -> One
    UniM x f   -> UniM (normal lv d book x) (normal lv d book f)
    Bit        -> Bit
    Bt0        -> Bt0
    Bt1        -> Bt1
    BitM x f t -> BitM (normal lv d book x) (normal lv d book f) (normal lv d book t)
    Nat        -> Nat
    Zer        -> Zer
    Suc n      -> Suc (normal lv d book n)
    NatM x z s -> NatM (normal lv d book x) (normal lv d book z) (normal lv d book s)
    Lst t      -> Lst (normal lv d book t)
    Nil        -> Nil
    Con h t    -> Con (normal lv d book h) (normal lv d book t)
    LstM x n c -> LstM (normal lv d book x) (normal lv d book n) (normal lv d book c)
    Enu s      -> Enu s
    Sym s      -> Sym s
    EnuM x c e -> EnuM (normal lv d book x) (map (\(s, t) -> (s, normal lv d book t)) c) (normal lv d book e)
    Sig a b    -> Sig (normal lv d book a) (normal lv d book b)
    Tup a b    -> Tup (normal lv d book a) (normal lv d book b)
    SigM x f   -> SigM (normal lv d book x) (normal lv d book f)
    All a b    -> All (normal lv d book a) (normal lv d book b)
    Lam k f    -> Lam k (\x -> normal 0 (d+1) book (f x)) -- note: uses lv=0 for finite pretty printing
    App f x    -> App (normal 1  d book f) (normal lv d book x)
    Eql t a b  -> Eql (normal lv d book t) (normal lv d book a) (normal lv d book b)
    Rfl        -> Rfl
    EqlM x f   -> EqlM (normal lv d book x) (normal lv d book f)
    Ind t      -> Ind (normal lv d book t)
    Frz t      -> Frz (normal lv d book t)
    Loc l t    -> Loc l (normal lv d book t)
    Rwt a b x  -> Rwt (normal lv d book a) (normal lv d book b) (normal lv d book x)
    Era        -> Era
    Sup l a b  -> Sup l (normal lv d book a) (normal lv d book b)
    Num t      -> Num t
    Val v      -> Val v
    Op2 o a b  -> Op2 o (normal lv d book a) (normal lv d book b)
    Op1 o a    -> Op1 o (normal lv d book a)
    Pri p      -> Pri p
    Met _ _ _  -> error "not-supported"
    Pat _ _ _  -> error "not-supported"

normalCtx :: Int -> Int -> Book -> Ctx -> Ctx
normalCtx lv d book (Ctx ctx) = Ctx (map normalAnn ctx)
  where normalAnn (k,v,t) = (k, normal lv d book v, normal lv d book t)
  where normalAnn (k,v,t) = (k, normal lv d book subs v, normal lv d book subs t)
