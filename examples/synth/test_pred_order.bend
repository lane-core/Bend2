gen test_pred_order(a : Nat, b : Nat) -> Nat

tst test_pred_order(2, 3) == 0 : Nat
tst test_pred_order(1, 3) == 2 : Nat
tst test_pred_order(2, 7) == 0 : Nat
tst test_pred_order(5, 8) == 7 : Nat

end
()
