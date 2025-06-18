{-./Type.hs-}
{-./WHNF.hs-}

module Core.Normal where

import Core.Type
import Core.WHNF

import Debug.Trace

normal :: Int -> Int -> Book -> Term -> Term
normal lv d book term =
  -- trace (">> " ++ show lv ++ " | " ++ show term ++ " ~> " ++ show (whnf lv book term)) $
  case whnf lv book term of
    Var k i   -> Var k i
    Ref k     -> Ref k
    Sub t     -> normal lv d book t
    Fix k f   -> Fix k (\x -> normal lv (d+1) book (f x))
    Let v f   -> Let (normal lv d book v) (normal lv d book f)
    Set       -> Set
    Ann x t   -> Ann (normal lv d book x) (normal lv d book t)
    Chk x t   -> Chk (normal lv d book x) (normal lv d book t)
    Emp       -> Emp
    Efq       -> Efq
    Uni       -> Uni
    One       -> One
    Use f     -> Use (normal lv d book f)
    Bit       -> Bit
    Bt0       -> Bt0
    Bt1       -> Bt1
    Bif f t   -> Bif (normal lv d book f) (normal lv d book t)
    Nat       -> Nat
    Zer       -> Zer
    Suc n     -> Suc (normal lv d book n)
    Swi z s   -> Swi (normal lv d book z) (normal lv d book s)
    Lst t     -> Lst (normal lv d book t)
    Nil       -> Nil
    Con h t   -> Con (normal lv d book h) (normal lv d book t)
    Mat n c   -> Mat (normal lv d book n) (normal lv d book c)
    Enu s     -> Enu s
    Sym s     -> Sym s
    Cse c     -> Cse (map (\(s, t) -> (s, normal lv d book t)) c)
    Sig a b   -> Sig (normal lv d book a) (normal lv d book b)
    Tup a b   -> Tup (normal lv d book a) (normal lv d book b)
    Get f     -> Get (normal lv d book f)
    All a b   -> All (normal lv d book a) (normal lv d book b)
    Lam k f   -> Lam k (\x -> normal 0 (d+1) book (f x)) -- note: uses lv=0 for finite pretty printing
    App f x   -> App (normal 0 d book f) (normal lv d book x)
    Eql t a b -> Eql (normal lv d book t) (normal lv d book a) (normal lv d book b)
    Rfl       -> Rfl
    Rwt f     -> Rwt (normal lv d book f)
    Ind t     -> Ind (normal lv d book t)
    Frz t     -> Frz (normal lv d book t)
    Loc l t   -> Loc l (normal lv d book t)
    Era       -> Era
    Sup l a b -> Sup l (normal lv d book a) (normal lv d book b)
    Met _ _ _ -> error "not-supported"
    Pat _ _ _ -> error "not-supported"
