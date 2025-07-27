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

def T0 : Nat{4n == add(1n, 3n)} = {==}
def T1 : Nat{0n == add(0n, 0n)} = {==}
def T2 : Nat{5n == add(2n, 3n)} = {==}
def T3 : Nat{10n == add(add(2n, 3n), 5n)} = ()
"""

main :: IO ()
main = testFileChecks add_bend
