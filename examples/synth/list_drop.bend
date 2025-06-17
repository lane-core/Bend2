gen list_drop(A: Set, b : ~Nat, c : A[]) -> A[]

tst list_drop(Nat, 3, [1, 2, 3]) == [] : Nat[]
tst list_drop(Bit, 2, [True, True, True, True]) == [True, True] : Bit[]
tst list_drop(Nat, 4, [1, 2]) == [] : Nat[]

end ()
