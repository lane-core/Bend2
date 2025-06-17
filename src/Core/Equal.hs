{-./Type.hs-}
{-./WHNF.hs-}

module Core.Equal where

import Debug.Trace

import Core.Type
import Core.WHNF

equal :: Int -> Book -> Term -> Term -> Bool
equal d book a b = eql 1 d book a b

eql :: Int -> Int -> Book -> Term -> Term -> Bool
eql 0  d book a b = cmp 0 d book (whnf 0 book a) (whnf 0 book b)
eql lv d book a b = eql (lv-1) d book a b || cmp lv d book (whnf lv book a) (whnf lv book b)

cmp :: Int -> Int -> Book -> Term -> Term -> Bool
cmp lv d book a b =
  -- trace ("E" ++ show lv ++ " " ++ show a ++ "\n== " ++ show b) $
  case (a , b) of
    (Fix ka fa    , Fix kb fb    ) -> eql lv d book (fa (fb (Var ka d))) (fb (fa (Var kb d)))
    (Fix ka fa    , b            ) -> eql lv d book (fa b) b
    (a            , Fix kb fb    ) -> eql lv d book a (fb (Fix kb fb))
    (Var ka ia    , Var kb ib    ) -> ia == ib
    (Ref ka       , Ref kb       ) -> ka == kb
    (Sub ta       , Sub tb       ) -> eql lv d book ta tb
    (Let va fa    , Let vb fb    ) -> eql lv d book va vb && eql lv d book fa fb
    (Set          , Set          ) -> True
    (Ann xa ta    , Ann xb tb    ) -> eql lv d book xa xb && eql lv d book ta tb
    (Chk xa ta    , Chk xb tb    ) -> eql lv d book xa xb && eql lv d book ta tb
    (Emp          , Emp          ) -> True
    (Efq          , Efq          ) -> True
    (Uni          , Uni          ) -> True
    (One          , One          ) -> True
    (Use fa       , Use fb       ) -> eql lv d book fa fb
    (Bit          , Bit          ) -> True
    (Bt0          , Bt0          ) -> True
    (Bt1          , Bt1          ) -> True
    (Bif fa ta    , Bif fb tb    ) -> eql lv d book fa fb && eql lv d book ta tb
    (Nat          , Nat          ) -> True
    (Zer          , Zer          ) -> True
    (Suc na       , Suc nb       ) -> eql lv d book na nb
    (Swi za sa    , Swi zb sb    ) -> eql lv d book za zb && eql lv d book sa sb
    (Lst ta       , Lst tb       ) -> eql lv d book ta tb
    (Nil          , Nil          ) -> True
    (Con ha ta    , Con hb tb    ) -> eql lv d book ha hb && eql lv d book ta tb
    (Mat na ca    , Mat nb cb    ) -> eql lv d book na nb && eql lv d book ca cb
    (Enu sa       , Enu sb       ) -> sa == sb
    (Sym sa       , Sym sb       ) -> sa == sb
    (Cse ca       , Cse cb       ) -> length ca == length cb && all (\ ((s1,t1), (s2,t2)) -> s1 == s2 && eql lv d book t1 t2) (zip ca cb)
    (Sig aa ba    , Sig ab bb    ) -> eql lv d book aa ab && eql lv d book ba bb
    (Tup aa ba    , Tup ab bb    ) -> eql lv d book aa ab && eql lv d book ba bb
    (Get fa       , Get fb       ) -> eql lv d book fa fb
    (All aa ba    , All ab bb    ) -> eql lv d book aa ab && eql lv d book ba bb
    (Lam ka fa    , Lam kb fb    ) -> eql lv (d+1) book (fa (Var ka d)) (fb (Var kb d))
    (App fa xa    , App fb xb    ) -> eql lv d book fa fb && eql lv d book xa xb
    (Eql ta aa ba , Eql tb ab bb ) -> eql lv d book ta tb && eql lv d book aa ab && eql lv d book ba bb
    (Rfl          , Rfl          ) -> True
    (Rwt fa       , Rwt fb       ) -> eql lv d book fa fb
    (Ind ta       , b            ) -> eql lv d book ta b
    (a            , Ind tb       ) -> eql lv d book a tb
    (Frz ta       , b            ) -> eql lv d book ta b
    (a            , Frz tb       ) -> eql lv d book a tb
    (Era          , Era          ) -> True
    (Sup la aa ba , Sup lb ab bb ) -> la == lb && eql lv d book aa ab && eql lv d book ba bb
    (Met _  _  _  , Met _  _  _  ) -> error "not-supported"
    (Pat _  _  _  , Pat _  _  _  ) -> error "not-supported"
    (_            , _            ) -> False
