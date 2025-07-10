# FIXME

# Fixed. Note: (a+b) for Nats requires Nat/add in context

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

def add_x_y (a:Nat, b:Nat) -> Nat{(a+b) == Nat/add(a,b)}:
  match a:
    case 0n:
      finally
    case 1n + p:
      finally
