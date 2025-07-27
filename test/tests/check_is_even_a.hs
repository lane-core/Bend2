{-# LANGUAGE MultilineStrings #-}

import Test

is_even_a_bend :: String
is_even_a_bend = """
def is_even_a(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n:
      False
    case 2n + p:
      is_even_a(p)

def T0 : Bool{True == is_even_a(0n)} = {==}
def T1 : Bool{False == is_even_a(1n)} = {==}
def T2 : Bool{True == is_even_a(4n)} = {==}
def T3 : Bool{False == is_even_a(5n)} = {==}
def T4 : Bool{True == is_even_a(6n)} = {==}
"""

main :: IO ()
main = testFileChecks is_even_a_bend