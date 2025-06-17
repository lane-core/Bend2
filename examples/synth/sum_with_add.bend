def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0:
      b
    case 1+a:
      1+add(a,b)

gen sum(xs: ~{Nat[]}) -> Nat {add}

tst sum([1,2,3]) == 6 : Nat
tst sum([3,2,2]) == 7 : Nat
tst sum([1,1,2]) == 4 : Nat
tst sum([4,2,3]) == 9 : Nat

end
()

