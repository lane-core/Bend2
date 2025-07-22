{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Core.LHS where

-- Import Data.Kind but hide Type to avoid conflict with Core.Type.Type
import Data.Kind (Type)
import qualified Data.Kind as DK

import Core.Type

-- Peano naturals at both type‑ and value‑level
data Nat = Z | S Nat

data SNat :: Nat -> DK.Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- Type‑level addition
type family Add (n :: Nat) (m :: Nat) :: Nat where
  Add Z     m = m
  Add (S n) m = S (Add n m)

addSNat :: SNat n -> SNat m -> SNat (Add n m)
addSNat SZ     m = m
addSNat (SS n) m = SS (addSNat n m)

-- Arg<n>  =  n‑ary function returning Term
type family Arg (n :: Nat) :: DK.Type where
  Arg Z     = Term
  Arg (S p) = Term -> Arg p

-- LHS = pair of arity and a constructor taking exactly that many args
data LHS where
  LHS :: SNat k -> (Term -> Arg k) -> LHS

lhs_ctr_new :: (Term -> Term) -> SNat n -> Arg n -> (Term -> Arg n)
lhs_ctr_new l SZ       ctr = \k -> App (l k) ctr
lhs_ctr_new l (SS n')  ctr = \x -> lhs_ctr_new l n' (ctr x)

lhs_ctr_ext :: SNat k -> (Term -> Arg (S k)) -> SNat n -> Arg n -> Arg (S (Add n k))
lhs_ctr_ext _ l SZ      ctr = l ctr
lhs_ctr_ext k l (SS n') ctr = \x -> lhs_ctr_ext k l n' (ctr x)

lhs_ctr :: LHS -> SNat n -> Arg n -> LHS
lhs_ctr (LHS k l) n ctr = case k of
  SZ    -> LHS n               (lhs_ctr_new l n ctr)
  SS k' -> LHS (addSNat n k')  (lhs_ctr_ext k' l n ctr)

getArgs :: Term -> [Term] -> [Term]
getArgs (App f a) acc = getArgs f (a:acc)
getArgs t         acc = t:acc

lhs_to_list :: LHS -> [Term]
lhs_to_list (LHS k l) = case k of
  SZ     -> getArgs (l Era) []
  SS _   -> []  -- unreachable per original spec
