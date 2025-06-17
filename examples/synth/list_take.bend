gen take(a : Set, b: ~Nat, c : a[], d: a[]) -> a[]

tst take(Bit, 2, [True, False, True], []) == [True, False] : Bit[]
tst take(Bit, 1, [True, False], []) == [True] : Bit[]
tst take(Nat, 3, [1, 3, 4, 5], []) == [1, 3, 4] : Nat[]

end
()
