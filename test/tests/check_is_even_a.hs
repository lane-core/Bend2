{-# LANGUAGE MultilineStrings #-}

import Test

is_even_a_bend :: String
is_even_a_bend = """
def is_even_a(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n:
      False
    case 2n + p:
      is_even_a(p)

assert True == is_even_a(0n) : Bool
assert False == is_even_a(1n) : Bool
assert True == is_even_a(4n) : Bool
assert False == is_even_a(5n) : Bool
assert True == is_even_a(6n) : Bool
"""

main :: IO ()
main = testFileChecks is_even_a_bend