def inj_left(a : (Nat & Nat)) -> Nat:
  match a:
    case (lft, rgt):
      lft

inj_left((1, 2))
