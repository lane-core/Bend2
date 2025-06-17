# Negation on booleans
# - not(True)  = False
# - not(False) = True
def not(x: Bool) -> Bool:
  match x:
    case False:
      True
    case True:
      False

# Proof: double negation is identity
def double_neg_theo(x: Bool) -> Bool{not(not(x)) == x}:
  match x:
    case False:
      {==}
    case True:
      {==}

# Congruence of equality
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  match e:
    case {==}:
      {==}

# Nat Parity (with nested match)
# - is_even_b(3) = False
# - is_even_b(4) = True
# - is_even_b(5) = False
# - is_even_b(6) = True
def is_even_a(n: Nat) -> Bool:
  match n:
    case 0:
      True
    case 1 + 0:
      False
    case 1 + 1 + p:
      is_even_a(p)

# Nat Parity (calling 'not')
# - is_even_b(3) = False
# - is_even_b(4) = True
# - is_even_b(5) = False
# - is_even_b(6) = True
def is_even_b(n: Nat) -> Bool:
  match n:
    case 0:
      True
    case 1 + p:
      not(is_even_b(p))

# Proof that both is_even implementations are identical
# (Can we have FunExt?)
def is_even_ab_theo(n: Nat) -> Bool{(is_even_a n) == (is_even_b n)}:
  match n:
    case 0:
      {==}
    case 1 + 0:
      {==}
    case 1 + 1 + p:
      let t = double_neg_theo(is_even_b(p));
      match t:
        case {==}:
          is_even_ab_theo(p)

is_even_ab_theo(3)
