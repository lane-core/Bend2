# FIXME

####

# can't infer when aliasing (inline use checks):

def thm(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  make_pair = λa1.λb1.(a1,b1)
  λI.I(Σa:A.B, make_pair)

  # ✗ thm
  # CantInfer:
  # Context:
  # - A : Set
  # - B : Set
  # Location: (line 8, column 15)
  # 8 |   make_pair = λa1.λb1.(a1,b1)

