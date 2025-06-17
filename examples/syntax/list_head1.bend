def list_head(a : Nat[], b : Nat) -> Nat:
  match a:
    case []:
      b
    case h <> t:
      h

list_head([1, 2, 3], 0)
