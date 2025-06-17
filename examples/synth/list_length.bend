gen list_length(A: Set, n: ~A[]) -> Nat

tst list_length(Bit, [True, False, True]) == 3 : Nat
tst list_length(Nat, [1, 1, 1, 1]) == 4 : Nat
tst list_length(Bit, []) == 0 : Nat

end
()