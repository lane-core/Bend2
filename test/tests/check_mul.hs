{-# LANGUAGE MultilineStrings #-}

import Test

mul_bend :: String
mul_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n + ap:
      add(b, mul(ap, b))

def T0 : Nat{0n == mul(0n, 5n)} = {==}
def T1 : Nat{0n == mul(3n, 0n)} = {==}
def T2 : Nat{6n == mul(2n, 3n)} = {==}
def T3 : Nat{12n == mul(3n, 4n)} = {==}
"""

main :: IO ()
main = testFileChecks mul_bend