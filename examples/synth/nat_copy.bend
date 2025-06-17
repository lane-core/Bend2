# copy: Nat -> (Pair Nat Nat)
# - copy(3)=(3,3)
# - copy(7)=(7,7)

gen copy(n : Nat) -> (Nat & Nat)

tst copy(3) == (3, 3) : (Nat & Nat)
tst copy(7) == (7, 7) : (Nat & Nat)

end
()
