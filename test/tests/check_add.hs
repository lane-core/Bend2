{-# LANGUAGE MultilineStrings #-}

import Test

add_bend :: String
add_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

assert 4n == add(1n, 3n) : Nat
assert 0n == add(0n, 0n) : Nat
assert 5n == add(2n, 3n) : Nat
assert 10n == add(add(2n, 3n), 5n) : Nat
"""

main :: IO ()
main = testFileChecks add_bend
