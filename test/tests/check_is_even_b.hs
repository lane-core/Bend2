{-# LANGUAGE MultilineStrings #-}

import Test

is_even_b_bend :: String
is_even_b_bend = """
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def is_even_b(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n + p:
      neg(is_even_b(p))

assert True == is_even_b(0n) : Bool
assert False == is_even_b(1n) : Bool
assert False == is_even_b(3n) : Bool
assert True == is_even_b(4n) : Bool
assert False == is_even_b(5n) : Bool
"""

main :: IO ()
main = testFileChecks is_even_b_bend