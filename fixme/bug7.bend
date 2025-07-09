# FIXME

###

# Nat Op2 still missing, this gives error

  # ✗ f
  # Mismatch:
  # - Goal: Num
  # - Type: Nat
  # Context:
  # - a : Nat
  # - b : Nat
  # Location: (line 17, column 3)
  # 17 |   a+b

def f(a:Nat, b:Nat) -> Nat:
  a+b

def main : Nat = f(1n,2n)
