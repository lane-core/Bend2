# FIXME

###

# lambda annotations can be overriden by context assumptions
# so the following checks, however Nat != A

def thm(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  unused_but_in_goal = Σa:A.B
  λI.I(Σa:A.B, λa1 : Nat.λb1.(a1,b1))
