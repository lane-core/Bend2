
gen list_inc(l : ~{Nat[]}) -> Nat[]

tst list_inc([])        == []        : Nat[]
tst list_inc([1, 2])    == [2, 3]    : Nat[]
tst list_inc([0, 0])    == [1, 1]    : Nat[]
tst list_inc([3, 4, 5]) == [4, 5, 6] : Nat[]

end
()

# λa.λ{[]:[];<>:λb.λc.+h<>(a t)
