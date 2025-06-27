{-./Type.hs-}
{-./WHNF.hs-}

module Core.Rewrite where

import Debug.Trace

import Core.Type
import Core.WHNF
import Core.Equal

rewrite :: Int -> Book -> Subs -> Term -> Term -> Term -> Term
rewrite d book subs old neo val
  | equal d book [] old val = neo
  | otherwise               = case whnf 3 d book subs val of
    -- TODO: pass through all constructors
    Suc x -> Suc $ rewriteGo d book subs old neo x
    _     -> rewriteGo d book subs old neo val

-- Recursively rewrites occurrences of 'old' with 'neo' in 'val'
rewriteGo :: Int -> Book -> Subs -> Term -> Term -> Term -> Term
rewriteGo d book subs old neo val = case val of
  Var k i    -> Var k i
  Ref k      -> Ref k
  Sub t      -> t
  Fix k f    -> Fix k (\x -> rewrite (d+1) book subs old neo (f x))
  Let v f    -> Let (rewrite d book subs old neo v) (rewrite d book subs old neo f)
  Set        -> Set
  Ann x t    -> Ann (rewrite d book subs old neo x) (rewrite d book subs old neo t)
  Chk x t    -> Chk (rewrite d book subs old neo x) (rewrite d book subs old neo t)
  Emp        -> Emp
  Efq        -> Efq
  Uni        -> Uni
  One        -> One
  -- Use f      -> Use (rewrite d book subs old neo f)
  UniM x f   -> UniM (rewrite d book subs old neo x) (rewrite d book subs old neo f)
  Bit        -> Bit
  Bt0        -> Bt0
  Bt1        -> Bt1
  -- Bif f t    -> Bif (rewrite d book subs old neo f) (rewrite d book subs old neo t)
  BitM x f t -> BitM (rewrite d book subs old neo x) (rewrite d book subs old neo f) (rewrite d book subs old neo t)
  Nat        -> Nat
  Zer        -> Zer
  Suc n      -> Suc (rewrite d book subs old neo n)
  -- Swi z s    -> Swi (rewrite d book subs old neo z) (rewrite d book subs old neo s)
  NatM x z s -> NatM (rewrite d book subs old neo x) (rewrite d book subs old neo z) (rewrite d book subs old neo s)
  Lst t      -> Lst (rewrite d book subs old neo t)
  Nil        -> Nil
  Con h t    -> Con (rewrite d book subs old neo h) (rewrite d book subs old neo t)
  -- Mat n c    -> Mat (rewrite d book subs old neo n) (rewrite d book subs old neo c)
  LstM x n c -> LstM (rewrite d book subs old neo x) (rewrite d book subs old neo n) (rewrite d book subs old neo c)
  Enu s      -> Enu s
  Sym s      -> Sym s
  -- Cse c e    -> Cse (map (\(s,t) -> (s, rewrite d book subs old neo t)) c) (rewrite d book subs old neo e)
  EnuM x c e -> EnuM (rewrite d book subs old neo x) (map (\(s,t) -> (s, rewrite d book subs old neo t)) c) (rewrite d book subs old neo e)
  Sig a b    -> Sig (rewrite d book subs old neo a) (rewrite d book subs old neo b)
  Tup a b    -> Tup (rewrite d book subs old neo a) (rewrite d book subs old neo b)
  -- Get f      -> Get (rewrite d book subs old neo f)
  SigM x f   -> SigM (rewrite d book subs old neo x) (rewrite d book subs old neo f)
  All a b    -> All (rewrite d book subs old neo a) (rewrite d book subs old neo b)
  Lam k f    -> Lam k (\x -> rewrite (d+1) book subs old neo (f x))
  App f x    -> App (rewrite d book subs old neo f) (rewrite d book subs old neo x)
  Eql t a b  -> Eql (rewrite d book subs old neo t) (rewrite d book subs old neo a) (rewrite d book subs old neo b)
  Rfl        -> Rfl
  -- Rwt f      -> Rwt (rewrite d book subs old neo f)
  EqlM x f   -> EqlM (rewrite d book subs old neo x) (rewrite d book subs old neo f)
  Ind t      -> Ind (rewrite d book subs old neo t)
  Frz t      -> Frz (rewrite d book subs old neo t)
  Loc l t    -> Loc l (rewrite d book subs old neo t)
  Era        -> Era
  Sup l a b  -> Sup l (rewrite d book subs old neo a) (rewrite d book subs old neo b)
  Num t      -> Num t
  Val v      -> Val v
  Op2 o a b  -> Op2 o (rewrite d book subs old neo a) (rewrite d book subs old neo b)
  Op1 o a    -> Op1 o (rewrite d book subs old neo a)
  Pri p      -> Pri p
  Met _ _ _  -> error "not-supported"
  Pat _ _ _  -> error "not-supported"

