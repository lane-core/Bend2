# FIXME

###

# (a+b) == add(a,b) can't be proven because (a+b) parses as (Op2 ADD)

  # ✗ f
  # Mismatch:
  # - Goal: Num
  # - Type: Nat
  # Context:
  # - a : Nat
  # - b : Nat
  # Location: (line 17, column 3)
  # 17 |   a+b

def add(a:Nat, b:Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p,b)

def add_x_y (a:Nat, b:Nat) -> Nat{(a+b) == add(a,b)}:
  match a:
    case 0n:
      finally
    case 1n + p:
      finally
