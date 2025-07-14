# FIXME

###

# ugly error message (and should there be an error at all?)

type Term:
  case @A:
  case @B:

def f(a: Term) -> Unit:
  match a:
    case @A{}: ()
    case a:
      match a:
        case @A{}: ()
        case @B{}: ()

  # ✗ f
  # Mismatch:
  # - Goal: Unit
  # - Type: (λ_. (λctr. ~ ctr { &A: Unit ; &B: Unit ; λ_. () })(_x3))(&A)
  # Context:
  # - a : Term
  # Location: (line 10, column 7)
  # 10 |       match a:
  # 11 |         case @A{}: ()
  # 12 |         case @B{}: ()
