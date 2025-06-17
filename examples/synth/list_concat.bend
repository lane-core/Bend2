gen list_concat(A: Set, b: ~A[], c: A[]) -> A[]

tst list_concat(Nat, [1, 2], [3, 4, 5]) == [1, 2, 3, 4, 5] : Nat[]
tst list_concat(Nat, [], [5, 2]) == [5, 2] : Nat[]
tst list_concat(Bit, [True], [False]) == [True, False] : Bit[]

end ()