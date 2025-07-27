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

def T0 : Nat{0n == pred(0n)} = {==}
def T1 : Nat{0n == pred(1n)} = {==}
def T2 : Nat{2n == pred(3n)} = {==}
def T3 : Nat{9n == pred(10n)} = {==}
"""

main :: IO ()
main = testFileChecks pred_bend
