# returns the relative signed distance between two nats as a pair

gen nat_dist(a: ~Nat, b: Nat) -> (Bit & Nat)

tst nat_dist(2,3) == (True, 1) : (Bit & Nat)
tst nat_dist(1,4) == (True, 3) : (Bit & Nat)
tst nat_dist(4,2) == (False, 2) : (Bit & Nat)

end
()
