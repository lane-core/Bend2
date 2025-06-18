{-./Type.hs-}

module Core.Bind where

import qualified Data.Map.Strict as M
import Core.Type

bind :: Term -> Term
bind term = binder 0 term [] M.empty

bindBook :: Book -> Book
bindBook (Book defs) = Book (M.map bindDefn defs)
  where bindDefn (term, typ) = (bind term, bind typ)

binder :: Int -> Term -> [Term] -> M.Map Name Term -> Term
binder lv term ctx vars = case term of
  Var k i   -> case M.lookup k vars of { Just t -> t ; Nothing -> Ref k }
  Ref k     -> Ref k
  Sub t     -> t
  Let v f   -> Let (binder lv v ctx vars) (binder lv f ctx vars)
  Fix k f   -> Fix k (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Set       -> Set
  Ann x t   -> Ann (binder lv x ctx vars) (binder lv t ctx vars)
  Chk x t   -> Chk (binder lv x ctx vars) (binder lv t ctx vars)
  Emp       -> Emp
  Efq       -> Efq
  Uni       -> Uni
  One       -> One
  Use f     -> Use (binder lv f ctx vars)
  Bit       -> Bit
  Bt0       -> Bt0
  Bt1       -> Bt1
  Bif f t   -> Bif (binder lv f ctx vars) (binder lv t ctx vars)
  Nat       -> Nat
  Zer       -> Zer
  Suc n     -> Suc (binder lv n ctx vars)
  Swi z s   -> Swi (binder lv z ctx vars) (binder lv s ctx vars)
  Lst t     -> Lst (binder lv t ctx vars)
  Nil       -> Nil
  Con h t   -> Con (binder lv h ctx vars) (binder lv t ctx vars)
  Mat n c   -> Mat (binder lv n ctx vars) (binder lv c ctx vars)
  Enu s     -> Enu s
  Sym s     -> Sym s
  Cse c     -> Cse (map (\(s, t) -> (s, binder lv t ctx vars)) c)
  Sig a b   -> Sig (binder lv a ctx vars) (binder lv b ctx vars)
  Tup a b   -> Tup (binder lv a ctx vars) (binder lv b ctx vars)
  Get f     -> Get (binder lv f ctx vars)
  All a b   -> All (binder lv a ctx vars) (binder lv b ctx vars)
  Lam k f   -> Lam k (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  App f x   -> App (binder lv f ctx vars) (binder lv x ctx vars)
  Eql t a b -> Eql (binder lv t ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  Rfl       -> Rfl
  Rwt f     -> Rwt (binder lv f ctx vars)
  Ind t     -> Ind (binder lv t ctx vars)
  Frz t     -> Frz (binder lv t ctx vars)
  Loc s t   -> Loc s (binder lv t ctx vars)
  Era       -> Era
  Sup l a b -> Sup l (binder lv a ctx vars) (binder lv b ctx vars)
  Met k t c -> Met k (binder lv t ctx vars) (map (\x -> binder lv x ctx vars) c)
  Pat s m c -> error "not-supported"
