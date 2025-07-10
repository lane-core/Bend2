# fixed

###

# this gives the error

  # PARSE_ERROR
  # unexpected 'N'
  # expecting pair
  #
  # At line 1, column 19:
  # 1 | def f() -> Nat & Nat:
  #                      ^ (color marker points here)

# unless we parenthesize the second Nat, to `Nat & (Nat)`
# even (Nat & Nat) fails the same way

def f() -> Nat & Nat:
  (0n,1n)
