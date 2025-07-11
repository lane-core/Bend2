# FIXME

###

# scoping of variables when printing a context isn't respected.
# notice in the following error that, in A{(a)((a,()))==a}, the first `a` should be function (Σa:A. Unit) -> A,
# while the second is an element of A, so each a should refer to a different variable, but doesn't

  # Mismatch:
  # - Goal: C
  # - Type: Unit
  # Context:
  # - A : Set
  # - C : Set
  # - nd : (∀C:Set. (∀a:((Σa:A. Unit) -> A). (∀a:A. A{(a)((a,()))==a}) -> C) -> C) -> (∀C:Set. (∀a:((Σa:A. Unit) -> A). (∀b:(Σa:A. Unit). Σa:A. Unit{((a)(b),())==b}) -> C) -> C) -> C
  # Location: (line 25, column 13)
  # 25 |     ,λC.λnd.()

# even if we enable printing the Int argument of the vars, they are the same, namely 0, for both a's:

  # - nd : (∀C:Set. (∀a:((Σa:A^0. Unit) -> A^0). (∀a:A^0. A^0{(a^0)((a^0,()))==a^0}) -> C^0) -> C^0) -> (∀C:Set. (∀a:((Σa:A^0. Unit) -> A^0). (∀b:(Σa:A^0. Unit). Σa:A^0. Unit{((a^0)(b^0),())==b^0}) -> C^0) -> C^0) -> C^1
  # Location: (line 25, column 13)
  # 25 |     ,λC.λnd.()

def thm<A>() -> Exists(A->Σa:A.Unit, λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:(Σa:A.Unit) . (Σa:A.Unit){f(g(b)) == b}))):
  existsIntro(
    A->Σa:A.Unit
    ,λf.And(Exists((Σa:A.Unit)->A, λg . ∀a:A . A{g(f(a)) == a}), Exists((Σa:A.Unit)->A, λg . ∀b:Σa:A.Unit . (Σa:A.Unit){f(g(b)) == b}))
    ,λa.(a,())
    ,λC.λnd.()
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

