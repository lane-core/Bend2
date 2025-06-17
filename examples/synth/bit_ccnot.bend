# Toffoli gate or controlled-controlled-not (two control bits and one target bit)

gen bit_ccnot(a: Bit, b: Bit, c: Bit) -> Bit

tst bit_ccnot(True, True, True) == False : Bit
tst bit_ccnot(True, True, False) == True : Bit
tst bit_ccnot(True, False, True) == True : Bit
tst bit_ccnot(True, False, False) == False : Bit
tst bit_ccnot(False, True, False) == False : Bit
tst bit_ccnot(False, True, True) == True : Bit
tst bit_ccnot(False, False, True) == True : Bit

end
()
