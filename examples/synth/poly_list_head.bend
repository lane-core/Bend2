gen list_head(a: Set, b: a, c : a[]) -> a

tst list_head(Nat, 0, []) == 0 : Nat
tst list_head(Bit, False, [True, False, False]) == True : Bit

end
()
