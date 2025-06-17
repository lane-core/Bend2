def list_append(a: Set, b: a, c: a[]) -> a[]:
  match c:
    case []:
      b <> []
    case h <> t:
      h <> list_append(a, b, t)

list_append(Nat, 1, [1, 2])
