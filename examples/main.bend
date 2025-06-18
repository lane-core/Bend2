# Negation on booleans
# - not(True)  = False
# - not(False) = True
def not(x: Bool) -> Bool:
  if x:
    False
  else:
    True

# Proof: double negation is identity
def double_neg_theo(x: Bool) -> Bool{not(not(x)) == x}:
  if x:
    {==}
  else:
    {==}

# Double of a Nat
# - mul2(3) = 6
# - mul2(4) = 8
# - mul2(5) = 10
def mul2(n: Nat) -> Nat:
  match n:
    case 0:
      0
    case 1 + p:
      1 + 1 + mul2(p)

# Half of a Nat
# - div2(3) = 1
# - div2(6) = 3
# - div2(8) = 4
def div2(n: Nat) -> Nat:
  match n:
    case 0:
      0
    case 1 + 0:
      0
    case 1 + 1 + p:
      1 + div2(p)

# Congruence of equality
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  {==} = e
  {==}

# Proof: n*2/2 = n (old method)
def div2_mul2_theo(n: Nat) -> Nat{div2(mul2(n)) == n}:
  match n:
    case 0:
      {==}
    case 1 + p:
      ind = div2_mul2_theo(p)
      prf = cong(Nat, Nat, div2(mul2(p)), p, λx. 1 + x, ind)
      prf

# Nat Equality
def equal(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0   0  : True
    case 1+a 0  : False
    case 0   1+b: False
    case 1+a 1+b: equal(a, b)

# Proof: n*2/2 = n (simpler method)
def div2_mul2_theo_2(n: Nat) -> Nat{(div2 (mul2 n)) == n}:
  match n:
    case 0:
      {==}
    case 1 + p:
      1 + div2_mul2_theo_2(p)

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
      {==} = double_neg_theo(is_even_b(p))
      is_even_ab_theo(p)

# Types Playground
# ----------------

# Can we encode inductive datatypes?

# data Vec (A : Set) : Nat -> Set where
#   nil : Vec A 0
#   con : all m (x : A) (xs : Vec A m) -> Vec A (suc m)
def Vec(A: Set, len: Nat) -> Set:
  any ctr: @{@Nil,@Cons}.
  match ctr:
    case @Nil: # Nil
      any eLen: Nat{len == 0}.
      Unit
    case @Cons: # Cons
      any tLen: Nat.
      any head: A.
      any tail: Vec(A,tLen).
      any eLen: Nat{len == 1+tLen}.
      Unit

def VecInd
  ( A: Set
  , P: all n:Nat xs:Vec(A,n). Set
  , N: P(0,(@Nil,{==},()))
  , C: all s:Nat x:A xs:Vec(A,s) . P(s,xs) -> P(1+s,(@Cons,s,x,xs,{==},()))
  , n: Nat
  , x: Vec(A,n)
  ) -> P(n,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          (e, ()) = fields
          {==} = e
          N
        case @Cons:
          (l, x, xs, e, ()) = fields
          {==} = e
          ind = VecInd(A,P,N,C,l,xs)
          C(l,x,xs)

def and1(a: Bool, b: Bool) -> Bool:
  match a b:
    case False _:
      True
    case True x :
      x
