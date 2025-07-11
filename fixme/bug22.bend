# FIXME

###

# necessity/possibility to inline subproofs behaves inconsistently from the perspective of the user
# the inconsistency is between the behavior in this issue vs the one in bug20.bend

# this (thm1) won't be able to infer the type of λb.(b,()), despite of the fact that
# if we write just λb.(), the error message says that b is of type A.

def thm1(A:Set) -> Exists(A->(Σa:A.Unit), λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:(Σa:A.Unit) . (Σa:A.Unit){f(g(b)) == b}))):
  existsIntro(
    A->Σa:A.Unit
    ,λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:(Σa:A.Unit) . (Σa:A.Unit){f(g(b)) == b}))
    ,λb.(b,())
    ,λC.λnd.nd(λC.λx.x(λp.~p{(,):λa.λu.a}, λa.finally),λC.λx.x(λp. ~p{(,):λa.λu.a}, λau.~au{(,):λa.λu. (~u{(): finally})}))
  )

  # CantInfer:
  # Context:
  # - A : Set
  # - nd : (∀C:Set. (∀a:((Σa:A. Unit) -> A). (∀a:A. A{(a)((a,()))==a}) -> C) -> C) -> (∀C:Set. (∀a:((Σa:A. Unit) -> A). (∀b:(Σa:A. Unit). (Σa:A. Unit){((a)(b),())==b}) -> C) -> C) -> C
  # - C : Set
  # - x : ∀a:((Σa:A. Unit) -> A). (∀a:A. A{(a)((a,()))==a}) -> C
  # - a : A
  # Location: (line 14, column 6)
  # 14 |     ,λb.(b,())

def thm2(A:Set) -> Exists(A->(Σa:A.Unit), λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:(Σa:A.Unit) . (Σa:A.Unit){f(g(b)) == b}))):
  existsIntro(
    A->Σa:A.Unit
    ,λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:(Σa:A.Unit) . (Σa:A.Unit){f(g(b)) == b}))
    ,λb.()
    ,λC.λnd.nd(λC.λx.x(λp.~p{(,):λa.λu.a}, λa.finally),λC.λx.x(λp. ~p{(,):λa.λu.a}, λau.~au{(,):λa.λu. (~u{(): finally})}))
  )

  # ✗ thm2
  # Mismatch:
  # - Goal: Σa:A. Unit
  # - Type: Unit
  # Context:
  # - A : Set
  # - b : A
  # Location: (line 32, column 9)
  # 32 |     ,λb.()

# so in this case we are obligated NOT to inline the function, which is the opposite of behavior from bug20.
# the following checks:

def forget_unit(B:Set) -> B -> Σb:B.Unit:
  λb.(b,())

def thm3(A:Set) -> Exists(A->(Σa:A.Unit), λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:(Σa:A.Unit) . (Σa:A.Unit){f(g(b)) == b}))):
  existsIntro(
    A->Σa:A.Unit
    ,λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:(Σa:A.Unit) . (Σa:A.Unit){f(g(b)) == b}))
    ,forget_unit(A)
    ,λC.λnd.nd(λC.λx.x(λp.~p{(,):λa.λu.a}, λa.finally),λC.λx.x(λp. ~p{(,):λa.λu.a}, λau.~au{(,):λa.λu. (~u{(): finally})}))
  )


# -------------------------------------------------------------------
#
# prelude (this can be ignored):
def And(A: Set, B: Set) -> Set:
  ∀C:Set. ((A -> B -> C) -> C)
def Exists(A : Set, P: A -> Set) -> Set:
  ∀C:Set . ((∀a:A . (P(a) -> C)) -> C)
def existsIntro : ∀A: Set . (∀P: A -> Set . (∀a:A . (∀pa:P(a) . (Exists(A,P))))) =
  λA.λP.λa.λpa.λC.λI.I(a)(pa)
