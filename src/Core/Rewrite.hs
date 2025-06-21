{-./Type.hs-}
{-./WHNF.hs-}
{-./Equal.hs-}

module Core.Rewrite where

import Debug.Trace

import Core.Type
import Core.WHNF
import Core.Equal

rewrite :: Int -> Book -> Term -> Term -> Term -> Term
rewrite d book old neo val
  | equal d book old val = neo
  | otherwise            = case whnf 2 book val of
    -- TODO: pass through all constructors
    Suc x -> Suc $ rewriteGo d book old neo x
    _     -> rewriteGo d book old neo val

-- Recursively rewrites occurrences of 'old' with 'neo' in 'val'
rewriteGo :: Int -> Book -> Term -> Term -> Term -> Term
rewriteGo d book old neo val = case val of
  Var k i   -> Var k i
  Ref k     -> Ref k
  Sub t     -> t
  Fix k f   -> Fix k (\x -> rewrite (d+1) book old neo (f x))
  Let v f   -> Let (rewrite d book old neo v) (rewrite d book old neo f)
  Set       -> Set
  Ann x t   -> Ann (rewrite d book old neo x) (rewrite d book old neo t)
  Chk x t   -> Chk (rewrite d book old neo x) (rewrite d book old neo t)
  Emp       -> Emp
  Efq       -> Efq
  Uni       -> Uni
  One       -> One
  Use f     -> Use (rewrite d book old neo f)
  Bit       -> Bit
  Bt0       -> Bt0
  Bt1       -> Bt1
  Bif f t   -> Bif (rewrite d book old neo f) (rewrite d book old neo t)
  Nat       -> Nat
  Zer       -> Zer
  Suc n     -> Suc (rewrite d book old neo n)
  Swi z s   -> Swi (rewrite d book old neo z) (rewrite d book old neo s)
  Lst t     -> Lst (rewrite d book old neo t)
  Nil       -> Nil
  Con h t   -> Con (rewrite d book old neo h) (rewrite d book old neo t)
  Mat n c   -> Mat (rewrite d book old neo n) (rewrite d book old neo c)
  Enu s     -> Enu s
  Sym s     -> Sym s
  Cse c     -> Cse (map (\(s, t) -> (s, rewrite d book old neo t)) c)
  Sig a b   -> Sig (rewrite d book old neo a) (rewrite d book old neo b)
  Tup a b   -> Tup (rewrite d book old neo a) (rewrite d book old neo b)
  Get f     -> Get (rewrite d book old neo f)
  All a b   -> All (rewrite d book old neo a) (rewrite d book old neo b)
  Lam k f   -> Lam k (\x -> rewrite (d+1) book old neo (f x))
  App f x   -> App (rewrite d book old neo f) (rewrite d book old neo x)
  Eql t a b -> Eql (rewrite d book old neo t) (rewrite d book old neo a) (rewrite d book old neo b)
  Rfl       -> Rfl
  Rwt f     -> Rwt (rewrite d book old neo f)
  Ind t     -> Ind (rewrite d book old neo t)
  Frz t     -> Frz (rewrite d book old neo t)
  Loc l t   -> Loc l (rewrite d book old neo t)
  Era       -> Era
  Sup l a b -> Sup l (rewrite d book old neo a) (rewrite d book old neo b)
  Met _ _ _ -> error "not-supported"
  Pat _ _ _ -> error "not-supported"
