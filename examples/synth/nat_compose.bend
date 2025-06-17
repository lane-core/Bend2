
def inc(a : Nat) -> Nat:
  1+a

def double(a : Nat) -> Nat:
  match a:
    case 0:
      0
    case 1+n:
      1+1+double(n)


gen compose(n: Nat -> Nat, m: Nat -> Nat, a : Nat) -> Nat

tst compose(inc, inc, 0) == 2 : Nat
tst compose(double, inc, 1) == 4 : Nat
tst compose(inc, double, 1) == 3 : Nat

end
()
