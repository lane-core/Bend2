
gen copy_to_pair(a : Nat) -> Σ(n: Nat).Nat

tst copy_to_pair(1) == (1, 1) : Σ(n: Nat).Nat
tst copy_to_pair(5) == (5, 5) : Σ(n: Nat).Nat

end
()
