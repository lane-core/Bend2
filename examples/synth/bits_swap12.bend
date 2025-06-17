gen swap12(a: Bit[]) -> Bit[]

tst swap12([]) == [] : Bit[]
tst swap12([True]) == [True] : Bit[]
tst swap12([False]) == [False] : Bit[]
tst swap12([True, False]) == [False, True] : Bit[]
tst swap12([False, True]) == [True, False] : Bit[]
tst swap12([True, False, True]) == [False, True, True] : Bit[]
tst swap12([False, True, True]) == [True, False, True] : Bit[]
tst swap12([True, False, False]) == [False, True, False] : Bit[]
tst swap12([False, True, False]) == [True, False, False] : Bit[]

end
()
