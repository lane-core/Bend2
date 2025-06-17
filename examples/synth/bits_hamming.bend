# requires @MAX_ELIM = 4 >= 4

gen bit_hamming(a: ~{Bit[]}, b: Bit[]) -> Nat

tst bit_hamming([True], [True]) == 0 : Nat
tst bit_hamming([True], [False]) == 1 : Nat
tst bit_hamming([False], [True]) == 1 : Nat
tst bit_hamming([False], [False]) == 0 : Nat
tst bit_hamming([False, True], [False, False]) == 1 : Nat
tst bit_hamming([False, False], [False, False]) == 0 : Nat
tst bit_hamming([False, False, True, False, True, False, False], [True, False, False, False, True, True, True]) == 4 : Nat

end
()
