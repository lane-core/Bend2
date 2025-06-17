gen poly_swap(a: Set, b: Set, c: (a & b)) -> (b & a)

tst poly_swap(Nat, Bit, (1, True)) == (True, 1) : (Bit & Nat)
tst poly_swap(Bit, Nat, (False, 2)) == (2, False) : (Nat & Bit)

end
()
