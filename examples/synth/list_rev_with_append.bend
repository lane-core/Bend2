def list_append(A: Set, b: A, c: A[]) -> A[]:
  match c:
    case []:
      b <> []
    case h <> t:
      h <> list_append(A, b, t)

gen list_rev(B: Set, l: ~B[]) -> B[] {list_append}

tst list_rev(Nat, [])                          == []                          : Nat[]
tst list_rev(Nat, [0])                         == [0]                         : Nat[]
tst list_rev(Nat, [0, 0, 1])                   == [1, 0, 0]                   : Nat[]
tst list_rev(Bit, [True, False, False, False]) == [False, False, False, True] : Bit[]

end
()