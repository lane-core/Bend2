gen bits_set_at(l: ~{Bit[]}, n: Nat) -> Bit[]

tst bits_set_at([True], 0)  == [True] : Bit[]
tst bits_set_at([False], 0) == [True] : Bit[]
tst bits_set_at([True, False, False, False, False], 3) == [True, False, False, True, False] : Bit[]

end
()
