
gen poly_swap(a: Set, b: (a & a)) -> (a & a)

tst poly_swap(Nat, (1, 2)) == (2, 1) : (Nat & Nat)
tst poly_swap(Bit, (False, True)) == (True, False) : (Bit & Bit)

end
()
