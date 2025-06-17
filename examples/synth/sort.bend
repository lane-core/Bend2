def inc_list(xs: Nat[]) -> Nat[]:
  match xs:
    case []:
      []
    case x<>xs:
      (1+x) <> inc_list(xs)

gen sort(fin: ~Nat, xs: ~Nat[], acc: Nat[]) -> Nat[]
  {inc_list}

tst sort(4, [3, 1, 2], []) == [1, 2, 3] : Nat[]
tst sort(4, [2, 3, 1], []) == [1, 2, 3] : Nat[]
tst sort(3, [2, 1]   , []) == [1, 2]    : Nat[]
tst sort(6, [5, 2, 4], []) == [2, 4, 5] : Nat[]

end
()
