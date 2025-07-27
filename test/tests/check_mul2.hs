{-# LANGUAGE MultilineStrings #-}

import Test

mul2_bend :: String
mul2_bend = """
def mul2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + p:
      2n + mul2(p)

assert 0n == mul2(0n) : Nat
assert 6n == mul2(3n) : Nat
assert 8n == mul2(4n) : Nat
assert 10n == mul2(5n) : Nat
"""

main :: IO ()
main = testFileChecks mul2_bend