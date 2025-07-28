def fixme/add_for_import(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      fixme/add_for_import(p,b)
