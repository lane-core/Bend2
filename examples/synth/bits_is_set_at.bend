gen bits_is_set_at(l: ~Bit[], n: Nat) -> Bit

tst bits_is_set_at([True], 0) == True : Bit
tst bits_is_set_at([False], 0) == False : Bit
tst bits_is_set_at([False, True], 1) == True : Bit
tst bits_is_set_at([True, False, False, False, False], 3) == False : Bit

end
()
