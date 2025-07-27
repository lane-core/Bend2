{-# LANGUAGE MultilineStrings #-}

import Test

pred_bend :: String
pred_bend = """
def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      return 0n
    case 1n + p:
      return p

assert 0n == pred(0n) : Nat
assert 0n == pred(1n) : Nat
assert 2n == pred(3n) : Nat
assert 9n == pred(10n) : Nat
"""

main :: IO ()
main = testFileChecks pred_bend
