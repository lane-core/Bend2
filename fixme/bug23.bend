# FIXME

# Fixed. comparison in `equal` is context dependent once we have local definitions
# because the defined variables can be equal to others not just by de brujin index,
# but also by the values they are defined to be. Store those values
# in context when checking a Let, then also check against them in equal.

###

# an unused variable causes a type mismatch by rewriting goal:

def thm(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  unused_but_in_goal = Σa:A.B
  λI.I(Σa:A.B, λa1.λb1.(a1,b1))

  # ✗ thm
  # Mismatch:
  # - Goal: unused_but_in_goal
  # - Type: A & B
  # Context:
  # - A : Set
  # - B : Set
  # - unused_but_in_goal : Set
  # - I : ∀C:Set. (A -> B -> C) -> C
  # - a1 : A
  # - b1 : B
  # Location: (line 7, column 24)
  # 7 |   λI.I(Σa:A.B, λa1.λb1.(a1,b1))
