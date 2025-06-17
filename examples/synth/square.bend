# square: Nat -> Nat
# - square(3) = 9
# - square(5) = 25
# - square(7) = 49
# - square(11) = 121

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0:
      b
    case 1+a:
      1+add(a,b)

def mul(a: Nat, b: Nat) -> Nat:
  match b:
    case 0:
      0
    case 1+n:
      add(a, mul(a, n))

gen square(n: ~Nat) -> Nat {mul}

tst square(3)  == 9 : Nat
tst square(2)  == 4 : Nat
tst square(5)  == 25 : Nat
tst square(7)  == 49 : Nat
tst square(11) == 121 : Nat

end
()
