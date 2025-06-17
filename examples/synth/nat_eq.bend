gen nat_eq(a: ~Nat, b: Nat) -> Bit

tst nat_eq(1, 1) == True : Bit
tst nat_eq(0, 1) == False : Bit
tst nat_eq(0, 0) == True : Bit
tst nat_eq(4, 5) == False : Bit
tst nat_eq(2, 5) == False : Bit
tst nat_eq(10, 11) == False : Bit
tst nat_eq(7, 7) == True : Bit
tst nat_eq(3, 3) == True : Bit

end
()

# ∅λa.λ{0:λ{0:#1;+:λb.#0};+:λ{0:λb.#1;+:λb.λc.((a b) c)}}
