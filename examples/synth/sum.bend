gen sum(xs: ~{~{Nat}[]}) -> Nat

tst sum([1,2,3]) == 6 : Nat
tst sum([3,2,2]) == 7 : Nat
tst sum([1,1,2]) == 4 : Nat
tst sum([4,2,3]) == 9 : Nat

end
()
