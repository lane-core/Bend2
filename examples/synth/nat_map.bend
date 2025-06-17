
def inc(n : Nat) -> Nat:
  1+n

def pred(m : Nat) -> Nat:
  match m:
    case 0:
      0
    case 1+n0:
      n0

gen nat_map(fn : (Nat -> Nat), a : ~Nat[]) -> Nat[]

tst nat_map(inc, [1, 2]) == [2, 3] : Nat[]
tst nat_map(pred, [4, 5, 6]) == [3, 4, 5] : Nat[]
tst nat_map(inc, [0, 5, 2]) == [1, 6, 3] : Nat[]

end
()
