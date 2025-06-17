# Double of a Nat
# - mul2(3) = 6
# - mul2(4) = 8
# - mul2(5) = 10
def mul2(n: Nat) -> Nat:
  match n:
    case 0:
      0
    case 1 + p:
      ↑↑mul2(p)

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
      ↑div2(p)

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

# Proof: n*2/2 = n (old method)
def div2_mul2_theo(n: Nat) -> Nat{div2(mul2(n)) == n}:
  match n:
    case 0:
      {==}
    case 1 + p:
      let ind = div2_mul2_theo(p)
      let prf = cong(Nat, Nat, div2(mul2(p)), p, λx. ↑x, ind)
      prf


div2_mul2_theo(2)


