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

def T0 : Nat{0n == mul2(0n)} = {==}
def T1 : Nat{6n == mul2(3n)} = {==}
def T2 : Nat{8n == mul2(4n)} = {==}
def T3 : Nat{10n == mul2(5n)} = {==}
"""

main :: IO ()
main = testFileChecks mul2_bend