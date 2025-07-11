# FIXME

###

# scoping of variables when printing a context isn't respected.
#
# notice in the error that in A{(a)((a,()))==a}
# the first `a` should be (Σa:A. Unit) -> A, and the second, A.
# both `a` there are actually the same variable

def exists(A: Set, P:A->Set) -> Set:
  Σa:A.P(a)

def thm(A:Set) -> exists((Σa:A.Unit)->A, λf.(∀a:A. A{f((a,())) == a})):
  ()

  # ✗ thm
  # Mismatch:
  # - Goal: Σa:((Σa:A^0. Unit) -> A^0). ∀a:A^0. A^0{(a^0)((a^0,()))==a^0}
  # - Type: Unit
  # Context:
  # - A : Set
  # Location: (line 16, column 3)
  # 16 |   ()
