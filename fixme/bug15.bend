# fixed
# was already working

###

# this isn't showing the full ctx
#
# introduced by commit 5020e1b6f13661e504f91cab95d957cdbedfc15b
# see bug15_2.bend too see the bug that motivated this commit

  # ✗ f
  # Mismatch:
  # - Goal: Unit
  # - Type: Bool
  # Context:
  # - x : Nat
  # - y : Nat
  # - z : Nat
  # Location: (line 8, column 3)
  # 8 |   True

# variables declared directly by assignments don't go into the contexts

def f() -> Unit:
  (x,y) = (1n,2n)
  z = 3n
  True
