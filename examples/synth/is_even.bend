
gen is_even(a: ~Nat, b: Bit) -> Bit

tst is_even(0, False) == True : Bit
tst is_even(1, False) == False : Bit
tst is_even(3, False) == False : Bit
tst is_even(4, False) == True : Bit

end
()

# isEven :: Int -> Bool -> Bool
# isEven n b = 
  # match n
    # 0: 
      # match b:
        # False: True
        # True: False
    # 1+p:
      # match b:
        # False:
          # isEven p True
        # True:
          # isEven p False

#case (n, b) of
#  (0, False) -> True
#  (0, True)  -> False
#  (m, _)     -> isEven (m - 1) (not b)
