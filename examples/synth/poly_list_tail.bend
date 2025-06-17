gen list_tail(a: Set, b: a[]) -> a[]

tst list_tail(Nat, []) == [] : Nat[]
tst list_tail(Bit, [True, False, False]) == [False, False] : Bit[]

end
()
