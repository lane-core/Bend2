gen list_replicate(A: Set, n: ~Nat, m: A) -> A[]

tst list_replicate(Nat, 3, 4) == [4, 4, 4] : Nat[]
tst list_replicate(Bit, 2, False) == [False, False] : Bit[]
tst list_replicate(Nat, 0, 2) == [] : Nat[]

end
()
