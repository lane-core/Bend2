gen bits_and(a: ~Bit[], b: Bit[]) -> Bit[]

tst bits_and([True], [False]) == [False] : Bit[]
tst bits_and([False], [True]) == [False] : Bit[]
tst bits_and([True, False, True], [True, True, False]) == [True, False, False] : Bit[]
tst bits_and([False, False, False], [True, True, True]) == [False, False, False] : Bit[]
tst bits_and([True, True, False, False], [True, False, True, False]) == [True, False, False, False] : Bit[]
tst bits_and([True, True, True, True], [False, True, False, True]) == [False, True, False, True] : Bit[]

end
()
