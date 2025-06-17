def cnot(a: Bit, b: Bit) -> Bit:
  if a:
    if b:
      False
    else:
      True
  else:
    b

gen bits_parity_with_cnot(bs: ~{Bit[]}) -> Bit {cnot}

tst bits_parity_with_cnot([True]) == True : Bit
tst bits_parity_with_cnot([False]) == False : Bit
tst bits_parity_with_cnot([True, True]) == False : Bit
tst bits_parity_with_cnot([False, True]) == True : Bit

end
()
