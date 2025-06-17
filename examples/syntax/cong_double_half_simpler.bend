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

# Proof: n*2/2 = n (simpler method)
def div2_mul2_theo_2(n: Nat) -> Nat{(div2 (mul2 n)) == n}:
  match n:
    case 0:
      {==}
    case 1 + p:
      ↑div2_mul2_theo_2(p)


div2_mul2_theo_2(4)
