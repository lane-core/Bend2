{-./Type.hs-}

module Core.WHNF where

import Debug.Trace

import Core.Type

import System.IO.Unsafe
import Data.IORef

whnf :: Int -> Book -> Term -> Term
whnf lv book term = do
  -- trace ("whnf " ++ show term) $
  case term of
    Let v f -> whnfLet lv book v f
    Ann x _ -> whnf lv book x
    Chk x _ -> whnf lv book x
    App f x -> whnfApp lv book (App f x) f x
    _       -> term

whnfLet :: Int -> Book -> Term -> Term -> Term
whnfLet lv book v f = whnf lv book (App f v)

whnfAppRef :: Int -> Book -> Term -> Name -> Term -> Term
whnfAppRef 0 book undo k x = App (Ref k) x
whnfAppRef 1 book undo k x = case deref book k of
  Just (term, _) -> whnfApp 1 book undo term x
  Nothing -> undo
whnfAppRef _ book undo k x = error "unreachable"

whnfApp :: Int -> Book -> Term -> Term -> Term -> Term
whnfApp lv book undo f x =
  case app (whnf lv book f) x of
    App (Bif _ _) x -> undo
    App (Swi _ _) x -> undo
    App (Mat _ _) x -> undo
    App (Cse _  ) x -> undo
    App (Use _  ) x -> undo
    App (Get _  ) x -> undo
    App (Rwt _  ) x -> undo
    res             -> res
  where
    app (Lam _ f  ) x = whnfAppLam lv book f x
    app (Sup l a b) x = error "not-supported"
    app (Fix k f  ) x = whnfAppFix lv book undo k f x
    app (Ref k    ) x = whnfAppRef lv book undo k x
    app (Use f    ) x = whnfAppUse lv book undo f x
    app (Bif f t  ) x = whnfAppBif lv book undo f t x
    app (Swi z s  ) x = whnfAppSwi lv book undo z s x
    app (Mat n c  ) x = whnfAppMat lv book undo n c x
    app (Cse c    ) x = whnfAppCse lv book undo c x
    app (Get f    ) x = whnfAppGet lv book undo f x
    app _           x = undo

whnfAppLam :: Int -> Book -> Body -> Term -> Term
whnfAppLam lv book f x = whnf lv book (f (whnf lv book x))

whnfAppFix :: Int -> Book -> Term -> String -> Body -> Term -> Term
whnfAppFix 0 book undo k f x = App (Fix k f) x
whnfAppFix 1 book undo k f x = whnfApp 1 book undo (f (Fix k f)) x
whnfAppFix _ book undo k f x = error "unreachable"

whnfAppUse :: Int -> Book -> Term -> Term -> Term -> Term
whnfAppUse lv book undo f x =
  case whnf lv book x of
    One -> whnf lv book f
    _   -> undo

whnfAppBif :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfAppBif lv book undo t0 t1 x =
  case whnf lv book x of
    Bt0 -> whnf lv book t0
    Bt1 -> whnf lv book t1
    _   -> undo

whnfAppSwi :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfAppSwi lv book undo z s x =
  case whnf lv book x of
    Zer       -> whnf lv book z
    Suc n     -> whnf lv book (App s (whnf lv book n))
    Sup l a b -> error "Sup interactions unsupported in Haskell"
    _         -> undo

whnfAppMat :: Int -> Book -> Term -> Term -> Term -> Term -> Term
whnfAppMat lv book undo n c x =
  case whnf lv book x of
    Nil       -> whnf lv book n
    Con h t   -> whnf lv book (App (App c (whnf lv book h)) (whnf lv book t))
    Sup l a b -> error "Sup interactions unsupported in Haskell"
    _         -> undo

whnfAppGet :: Int -> Book -> Term -> Term -> Term -> Term
whnfAppGet lv book undo f x =
  case whnf lv book x of
    Tup a b -> whnf lv book (App (App f (whnf lv book a)) (whnf lv book b))
    _       -> undo

whnfAppCse :: Int -> Book -> Term -> [(String, Term)] -> Term -> Term
whnfAppCse lv book undo c x =
  case whnf lv book x of
    Sym s -> case lookup s c of
      Just t  -> whnf lv book t
      Nothing -> undo
    _ -> undo

force :: Book -> Term -> Term
force book t =
  case whnf 1 book t of
    Ind t -> force book t
    Frz t -> force book t
    t     -> t
