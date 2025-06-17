gen list_at(A: Set, b: ~Nat, c : A[]) -> A[]

tst list_at(Nat, 2, [1, 2, 3]) == [3] : Nat[]
tst list_at(Nat, 3, [1, 2, 3]) == [] : Nat[]
tst list_at(Bit, 0, [False, True, True]) == [False] : Bit[]

end ()