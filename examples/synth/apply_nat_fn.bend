
def inc(n : Nat) -> Nat:
  ↑n

gen apply(f : (Nat -> Nat), a : Nat) -> Nat

tst apply(inc, 1) == 2 : Nat
tst apply(inc, 3) == 4 : Nat
tst apply(inc, 5) == 6 : Nat

end
()
