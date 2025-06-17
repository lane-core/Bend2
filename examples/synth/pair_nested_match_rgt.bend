gen pair_nested(a: (Nat & Nat)) -> Nat

tst pair_nested((1, 2)) == 0 : Nat
tst pair_nested((3, 0)) == 3 : Nat
tst pair_nested((7, 3)) == 0 : Nat
tst pair_nested((11, 0)) == 11 : Nat

end
()

