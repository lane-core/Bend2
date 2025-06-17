def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0:
      b
    case 1+a:
      1+add(a,b)

gen mul(x: ~Nat, y: Nat) -> Nat {add}

tst mul(2,3) == 6 : Nat
tst mul(4,2) == 8 : Nat
tst mul(1,1) == 1 : Nat
tst mul(3,1) == 3 : Nat

end
()
