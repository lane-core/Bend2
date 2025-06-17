
def inc(n : Nat) -> Nat:
  1+n

def pred(m : Nat) -> Nat:
  match m:
    case 0:
      0
    case 1+n0:
      n0

def toBool(n : Nat) -> Bit:
  match n:
    case 0:
      True
    case 1+n1:
      False

gen map(A: Set, B: Set, c : (A -> B), d : ~{A[]}) -> B[]

tst map(Nat, Nat, inc, [1, 2]) == [2, 3] : Nat[]
tst map(Nat, Nat, inc, [0, 5, 2]) == [1, 6, 3] : Nat[]
tst map(Nat, Bit, toBool, [1, 0]) == [False, True] : Bit[]

end
()

