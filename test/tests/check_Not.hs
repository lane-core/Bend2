{-# LANGUAGE MultilineStrings #-}

import Test

not_bend :: String
not_bend = """
def Not(A: Set) -> Set:
  A -> Empty

def T0 : Set{Not(Empty) == (Empty -> Empty)} = {==}
def T1 : Set{Not(Nat) == (Nat -> Empty)} = {==}
def T2 : Set{Not(Bool) == (Bool -> Empty)} = {==}
def T3 : Set{Not(Not(Bool)) == ((Bool -> Empty) -> Empty)} = {==}
"""

main :: IO ()
main = testFileChecks not_bend