gen sub(x: ~Nat, y: Nat) -> Nat

tst sub(0,  1)  == 0 : Nat
tst sub(1,  0)  == 1 : Nat
tst sub(5,  3)  == 2 : Nat
tst sub(10, 3)  == 7 : Nat
tst sub(20, 3)  == 17 : Nat
tst sub(19, 14) == 5 : Nat

end
()
