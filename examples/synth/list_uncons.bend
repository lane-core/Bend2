gen list_uncons(A: Set, b: A[], default: A) -> (A & A[])

tst list_uncons(Nat, [1, 2, 3], 0) == (1, [2, 3]) : (Nat & Nat[])
tst list_uncons(Nat, [], 3) == (3, []) : (Nat & Nat[])
tst list_uncons(Bit, [True, True], False) == (True, [True]) : (Bit & Bit[])

end
()
