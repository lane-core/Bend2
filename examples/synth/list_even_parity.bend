gen even_parity(a : ~{Bit[]}) -> Bit

tst even_parity([])                  == True  : Bit
tst even_parity([False, True])       == False : Bit
tst even_parity([False])             == True  : Bit
tst even_parity([False, False])      == True  : Bit
tst even_parity([True])              == False : Bit
tst even_parity([True, True, False]) == True  : Bit

end
()
