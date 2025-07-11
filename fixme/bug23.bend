# FIXME

# uncommenting a line with an unused variable causes a type mismatch:

def unit() -> And(∀a:Nat . Nat{add(0n,a) == a}, ∀a:Nat . Nat{add(a,0n) == a}):
  unused = unit_right_definition(Nat,add,0n)
  andIntro<∀a:Nat . Nat{add(0n,a) == a},∀a:Nat . Nat{add(a,0n) == a}>(λa.finally, add_unit_right)

def unit_right_definition<A>(f: A->A->A, u:A) -> Set:
  ∀a:A . A{f(a,u) == a}

  # ✗ unit
  # Mismatch:
  # - Goal: Σa:(∀a:Nat. Nat{a==a}). unused
  # - Type: Σa:(∀a:Nat. Nat{a==a}). ∀a:Nat. Nat{add(a,0n)==a}
  # Context:
  # - unused : Set
  # Location: (line 8, column 3)
  # 8 |   andIntro<∀a:Nat . Nat{add(0n,a) == a},∀a:Nat . Nat{add(a,0n) == a}>(λa.finally, add_unit_right)

# - this error disappears if we comment the `unused = ...` line

# -------------------------------------------------------------------
#
# prelude (this can be ignored):

def And<A,B>() -> Set:
  Σa:A.B

def andIntro<A,B>() -> ∀a:A . ∀b:B . And(A,B):
  λa.λb.(a,b)

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_unit_right() -> ∀a:Nat . Nat{add(a,0n) == a}:
  λa.
  match a:
    case 0n:
      finally
    case 1n + ap:
      ind = add_unit_right(ap)
      rewrite ind finally
