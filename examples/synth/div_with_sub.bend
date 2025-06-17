def sub(a: Nat, b: Nat) -> Nat:
  match a:
    case 0:
      0
    case 1+n:
      match b:
        case 0:
          1+n
        case 1+n1:
          sub(n, n1)

gen div(x: ~Nat, y: Nat) -> Nat {sub}

tst div(1, 0) == 0 : Nat
tst div(0, 1) == 1 : Nat
tst div(6, 3) == 2 : Nat
tst div(10, 3) == 3 : Nat
tst div(12, 4) == 3 : Nat

end
()
