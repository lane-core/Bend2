# FIXME

###

# can't infer type of inlined function λa.a

def thm1(A:Set) -> Σf: A->A . Σg:A->A . ∀a:A . A{g(f(a)) == a}:
  (λa.a,λb.b,λc.finally)
  # (id(A),λb.b,λc.finally)

def id(B:Set, b:B) -> B:
  b

  # ✗ thm1
  # CantInfer:
  # Context:
  # - A : Set
  # - c : A
  # Location: (line 8, column 4)
  # 8 |   (λa.a,λb.b,λc.finally)
