{-# LANGUAGE MultilineStrings #-}

import Test

div2_bend :: String
div2_bend = """
def div2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      0n
    case 2n + p:
      1n + div2(p)

assert 0n == div2(0n) : Nat
assert 0n == div2(1n) : Nat
assert 1n == div2(3n) : Nat
assert 3n == div2(6n) : Nat
assert 4n == div2(8n) : Nat
"""

main :: IO ()
main = testFileChecks div2_bend
