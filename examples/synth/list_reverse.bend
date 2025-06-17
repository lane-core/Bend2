gen reverse(A : Set, b : ~A[], c: A[]) -> A[]

tst reverse(Nat, [1, 2, 3], []) == [3, 2, 1] : Nat[]
tst reverse(Bit, [True, False], []) == [False, True] : Bit[]

end
()