{-# LANGUAGE MultilineStrings #-}

import Test

is_even_b_bend :: String
is_even_b_bend = """
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def is_even_b(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n + p:
      neg(is_even_b(p))

def T0 : Bool{True == is_even_b(0n)} = {==}
def T1 : Bool{False == is_even_b(1n)} = {==}
def T2 : Bool{False == is_even_b(3n)} = {==}
def T3 : Bool{True == is_even_b(4n)} = {==}
def T4 : Bool{False == is_even_b(5n)} = {==}
"""

main :: IO ()
main = testFileChecks is_even_b_bend