def inc(n : Nat) -> Nat:
  1+n

def pred(m : Nat) -> Nat:
  match m:
    case 0:
      0
    case 1+n0:
      n0

gen map(fn : (Nat -> Nat), d : ~Nat[]) -> Nat[]

tst map(inc, [1, 2]) == [2, 3] : Nat[]
tst map(inc, [0, 5, 2]) == [1, 6, 3] : Nat[]
tst map(pred, [1, 1, 1]) == [0, 0, 0] : Nat[]

end
()
