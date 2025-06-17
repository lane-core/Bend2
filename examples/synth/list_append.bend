gen list_append(A: Set, b: A, c: ~A[]) -> A[]

tst list_append(Nat, 3, [1, 2]) == [1, 2, 3] : Nat[]
tst list_append(Bit, False, [True]) == [True, False] : Bit[]
tst list_append(Nat, 1, [1, 2, 3, 4]) == [1, 2, 3, 4, 1] : Nat[]

end
()
