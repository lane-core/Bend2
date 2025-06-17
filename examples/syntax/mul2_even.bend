# Negation on booleans
# - not(True)  = False
# - not(False) = True
def not(x: Bool) -> Bool:
  match x:
    case False:
      True
    case True:
      False

def mul2(n: Nat) -> Nat:
  match n:
    case 0:
      0
    case 1 + p:
      ↑↑mul2(p)



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
def is_even(n: Nat) -> Bool:
  match n:
    case 0:
      True
    case 1 + 0:
      False
    case 1 + 1 + p:
      is_even(p)

def mul2_even_theo(n: Nat) -> Bool{is_even(mul2(n)) == True}:
  match n:
    case 0: {==}  # is_even(0) = True
    case 1 + p: mul2_even_theo(p)  # is_even(2 + mul2(p)) = is_even_a(mul2(p))

mul2_even_theo(4)
