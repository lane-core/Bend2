{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Equal where

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import Data.Maybe (fromMaybe, isNothing)
import Control.Applicative
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

import Core.Type
import Core.WHNF

import Debug.Trace

-- Equality
-- ========

equal :: Int -> Book -> Ctx -> Term -> Term -> Bool
equal d book ctx a b = eql 3 d book ctx a b

eql :: Int -> Int -> Book -> Ctx -> Term -> Term -> Bool
eql 0  d book ctx a b = cmp 0 d book ctx (cut a) (cut b)
eql lv d book ctx a b = identical || similar where
  identical = eql 0 d book ctx a b
  similar   = cmp lv d book ctx (force book a) (force book b)

cmp :: Int -> Int -> Book -> Ctx -> Term -> Term -> Bool
cmp lv d book ctx a b =
  case (a , b) of
    (Fix ka fa    , Fix kb fb    ) -> eql lv d book ctx (fa (fb (Var ka d))) (fb (fa (Var kb d)))
    (Fix ka fa    , b            ) -> eql lv d book ctx (fa b) b
    (a            , Fix kb fb    ) -> eql lv d book ctx a (fb (Fix kb fb))
    (Ref ka       , Ref kb       ) -> ka == kb
    (Ref ka       , b            ) -> case deref book ka of { Just (_, term, _) -> eql lv d book ctx term b ; Nothing -> False }
    (a            , Ref kb       ) -> case deref book kb of { Just (_, term, _) -> eql lv d book ctx a term ; Nothing -> False }
    (Var ka ia    , Var kb ib    ) -> ia == ib
    (Var ka ia    , _            ) ->
      let Ctx ks = ctx in
      if ia < length ks
         then let (n, v, vt) = ks !! ia in
            case v of
            Var _ _ -> False
            _       -> cmp lv d book ctx v b
         else False
    (_             , Var kb ib   ) ->
      let Ctx ks = ctx in
      if ib < length ks
         then let (n, v, vt) = ks !! ib in
            case v of
            Var _ _ -> False
            _       -> cmp lv d book ctx a v
         else False
    (Sub ta       , Sub tb       ) -> eql lv d book ctx ta tb
    (Let va fa    , Let vb fb    ) -> eql lv d book ctx va vb && eql lv d book ctx fa fb
    (Set          , Set          ) -> True
    (Chk xa ta    , Chk xb tb    ) -> eql lv d book ctx xa xb && eql lv d book ctx ta tb
    (Emp          , Emp          ) -> True
    (EmpM xa      , EmpM xb      ) -> eql lv d book ctx xa xb
    (Uni          , Uni          ) -> True
    (One          , One          ) -> True
    (UniM xa fa   , UniM xb fb   ) -> eql lv d book ctx xa xb && eql lv d book ctx fa fb
    (Bit          , Bit          ) -> True
    (Bt0          , Bt0          ) -> True
    (Bt1          , Bt1          ) -> True
    (BitM xa fa ta, BitM xb fb tb) -> eql lv d book ctx xa xb && eql lv d book ctx fa fb && eql lv d book ctx ta tb
    (Nat          , Nat          ) -> True
    (Zer          , Zer          ) -> True
    (Suc na       , Suc nb       ) -> eql lv d book ctx na nb
    (NatM xa za sa, NatM xb zb sb) -> eql lv d book ctx xa xb && eql lv d book ctx za zb && eql lv d book ctx sa sb
    (Lst ta       , Lst tb       ) -> eql lv d book ctx ta tb
    (Nil          , Nil          ) -> True
    (Con ha ta    , Con hb tb    ) -> eql lv d book ctx ha hb && eql lv d book ctx ta tb
    (LstM xa na ca, LstM xb nb cb) -> eql lv d book ctx xa xb && eql lv d book ctx na nb && eql lv d book ctx ca cb
    (Enu sa       , Enu sb       ) -> sa == sb
    (Sym sa       , Sym sb       ) -> sa == sb
    (EnuM xa ca da, EnuM xb cb db) -> eql lv d book ctx xa xb && length ca == length cb && all (\ ((s1,t1), (s2,t2)) -> s1 == s2 && eql lv d book ctx t1 t2) (zip ca cb) && eql lv d book ctx da db
    (Sig aa ba    , Sig ab bb    ) -> eql lv d book ctx aa ab && eql lv d book ctx ba bb
    (Tup aa ba    , Tup ab bb    ) -> eql lv d book ctx aa ab && eql lv d book ctx ba bb
    (SigM xa fa   , SigM xb fb   ) -> eql lv d book ctx xa xb && eql lv d book ctx fa fb
    (All aa ba    , All ab bb    ) -> eql lv d book ctx aa ab && eql lv d book ctx ba bb
    (Lam ka ta fa , Lam kb tb fb ) -> eql lv (d+1) book ctx (fa (Var ka d)) (fb (Var kb d)) && fromMaybe True (liftA2 (eql lv d book ctx) ta tb)
    (App fa xa    , App fb xb    ) -> eql lv d book ctx fa fb && eql lv d book ctx xa xb
    (Eql ta aa ba , Eql tb ab bb ) -> eql lv d book ctx ta tb && eql lv d book ctx aa ab && eql lv d book ctx ba bb
    -- (Eql ta _  _  , b            ) -> eql lv d book ctx ta b
    -- (a            , Eql tb _  _  ) -> eql lv d book ctx a tb
    (Rfl          , Rfl          ) -> True
    (EqlM xa fa   , EqlM xb fb   ) -> eql lv d book ctx xa xb && eql lv d book ctx fa fb
    (Ind ta       , b            ) -> eql lv d book ctx ta b
    (a            , Ind tb       ) -> eql lv d book ctx a tb
    (Frz ta       , b            ) -> eql lv d book ctx ta b
    (a            , Frz tb       ) -> eql lv d book ctx a tb
    (Loc _ ta     , b            ) -> eql lv d book ctx ta b
    (a            , Loc _ tb     ) -> eql lv d book ctx a tb
    (Rwt _ _ xa   , _            ) -> eql lv d book ctx xa b
    (_            , Rwt _ _ xb   ) -> eql lv d book ctx a xb
    (Era          , Era          ) -> True
    (Sup la aa ba , Sup lb ab bb ) -> eql lv d book ctx la lb && eql lv d book ctx aa ab && eql lv d book ctx ba bb
    (SupM xa la fa, SupM xb lb fb) -> eql lv d book ctx xa xb && eql lv d book ctx la lb && eql lv d book ctx fa fb
    (Frk la aa ba , Frk lb ab bb ) -> eql lv d book ctx la lb && eql lv d book ctx aa ab && eql lv d book ctx ba bb
    (Num ta       , Num tb       ) -> ta == tb
    (Val va       , Val vb       ) -> va == vb
    (Op2 oa aa ba , Op2 ob ab bb ) -> oa == ob && eql lv d book ctx aa ab && eql lv d book ctx ba bb
    (Op1 oa aa    , Op1 ob ab    ) -> oa == ob && eql lv d book ctx aa ab
    (Pri pa       , Pri pb       ) -> pa == pb
    (Met _  _  _  , Met _  _  _  ) -> error "not-supported"
    (Pat _  _  _  , Pat _  _  _  ) -> error "not-supported"
    (_            , _            ) -> False
