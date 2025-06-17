
gen bit_impl(a: Bit, b: Bit) -> Bit

tst bit_impl(True,  True)  == True  : Bit
tst bit_impl(True,  False) == False : Bit
tst bit_impl(False, True)  == True : Bit
tst bit_impl(False, False) == True : Bit

end
()
