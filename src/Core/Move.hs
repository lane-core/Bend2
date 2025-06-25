{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Move (move, moveBook) where

import qualified Data.Map as M
import Debug.Trace

import Core.Type

-- Auto-Move variables, linearizing/specializing them.
-- Currently, only enabled for the second field of pairs:
-- λ{ (,): λx.λy.(λ{ P0:B0 … Pn:Bn } x) }
-- -----------------------------------------
-- λ{ (,): λx.(λ{ P0:λy.B0 … Pn:λy.Bn } x) }

move :: Term -> Term
-- move t = t
move (Loc s t)   = Loc s (move t)
-- move (Get f)     = trace ("from:\n- " ++ show (Get f) ++ "\n- " ++ show (Get (moveGet f))) (Get (moveGet f))
move (Get f)     = Get (moveGet f)
move (Lam n b)   = Lam n (move . b)
move (App f x)   = App (move f) (move x)
move (Let v f)   = Let (move v) (move f)
move (Fix n b)   = Fix n (move . b)
move (Ann x t)   = Ann (move x) (move t)
move (Chk x t)   = Chk (move x) (move t)
move (Bif f t)   = Bif (move f) (move t)
move (Swi z s)   = Swi (move z) (move s)
move (Mat n c)   = Mat (move n) (move c)
move (Cse c d)   = Cse [ (tag, move br) | (tag,br) <- c ] (move d)
move (Use f)     = Use (move f)
move (Sig a b)   = Sig (move a) (move b)
move (All a b)   = All (move a) (move b)
move (Tup a b)   = Tup (move a) (move b)
move (Con h t)   = Con (move h) (move t)
move (Suc n)     = Suc (move n)
move (Lst t)     = Lst (move t)
move (Eql t a b) = Eql (move t) (move a) (move b)
move (Rwt f)     = Rwt (move f)
move (Ind t)     = Ind (move t)
move (Frz t)     = Frz (move t)
move (Sup l a b) = Sup l (move a) (move b)
move (Met n t x) = Met n (move t) (map move x)
move (Pat x m c) = Pat (map move x) [ (n, move m) | (n,m) <- m ] [ (map move ps, move br) | (ps,br) <- c ]
move t           = t

moveGet :: Term -> Term
moveGet term@(cut -> Lam x (bod x -> Lam y (bod y -> App (cut -> f) (cut -> Var x' _))))
  | x == x'   = Lam x (\_ -> App (putLam y f) (Var x 0))
  | otherwise = term
moveGet term = term

putLam :: Name -> Term -> Term
putLam y t = case t of
  Loc s t -> Loc s (putLam y t)
  Use f   -> Use (putLamAfter 0 y f)
  Bif t f -> Bif (putLamAfter 0 y t) (putLamAfter 0 y f)
  Swi z s -> Swi (putLamAfter 0 y z) (putLamAfter 1 y s)
  Mat n c -> Mat (putLamAfter 0 y n) (putLamAfter 2 y c)
  Cse c d -> Cse [ (tag, putLamAfter 0 y b) | (tag, b) <- c ] (putLamAfter 0 y d)
  Rwt f   -> Rwt (putLamAfter 0 y f)
  Get f   -> Get (putLamAfter 2 y f)
  t       -> t
  where putLamAfter :: Int -> Name -> Term -> Term
        putLamAfter 0 y t         = Lam y $ \x -> t
        putLamAfter n y (Lam k t) = Lam k $ \x -> putLamAfter (n-1) y (t x)
        putLamAfter n y t         = Lam k $ \x -> putLamAfter (n-1) y (App t (Var k 0))
                          where k = "_" ++ show n

moveBook :: Book -> Book
moveBook (Book defs) = Book (M.map moveDefn defs)
  where moveDefn (inj, term, typ) = (inj, move term, move typ)

-- Utils
-- -----

bod :: Name -> (Term -> Term) -> Term
bod = \ x f -> cut (f (Var x 0))
