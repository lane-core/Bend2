gen bit_not(a : ~{Bit[]}) -> Bit[]

tst bit_not([True, True, True]) == [False, False, False] : Bit[]
tst bit_not([True, False]) == [False, True] : Bit[]
tst bit_not([True, False, True]) == [False, True, False] : Bit[]

end
()
