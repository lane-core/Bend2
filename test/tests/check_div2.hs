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

def T0 : Nat{0n == div2(0n)} = {==}
def T1 : Nat{0n == div2(1n)} = {==}
def T2 : Nat{1n == div2(3n)} = {==}
def T3 : Nat{3n == div2(6n)} = {==}
def T4 : Nat{4n == div2(8n)} = {==}
"""

main :: IO ()
main = testFileChecks div2_bend
