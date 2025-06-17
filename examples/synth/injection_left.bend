gen injLeft(a: (Nat & Nat)) -> Nat

tst injLeft((2,3)) == 2 : Nat
tst injLeft((4,2)) == 4 : Nat
tst injLeft((1,1)) == 1 : Nat
tst injLeft((3,1)) == 3 : Nat

end
()
