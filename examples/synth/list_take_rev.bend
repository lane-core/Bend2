# tkr: Nat -> List Bool -> List Bool
# - tkr(2,[T,F,T],[])=[F,T]
# - tkr(1,[T,F],[])=[T]
# - tkr(0,[T,F],[])=[]
# - tkr(3,[F,T,T,F,T],[])=[T,T,F]

gen take_reverse(n : ~Nat, b : Bit[], c : Bit[]) -> Bit[]

tst take_reverse(2, [True, False, True], []) == [False, True] : Bit[]
tst take_reverse(1, [True, False], []) == [True] : Bit[]
tst take_reverse(0, [True, False], []) == [] : Bit[]
tst take_reverse(3, [False, True, True, False, True], []) == [True, True, False] : Bit[]

end
()

