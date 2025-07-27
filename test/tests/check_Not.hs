{-# LANGUAGE MultilineStrings #-}

import Test

not_bend :: String
not_bend = """
def Not(A: Set) -> Set:
  A -> Empty

assert Not(Empty) == (Empty -> Empty) : Set
assert Not(Nat) == (Nat -> Empty) : Set
assert Not(Bool) == (Bool -> Empty) : Set
assert Not(Not(Bool)) == ((Bool -> Empty) -> Empty) : Set
"""

main :: IO ()
main = testFileChecks not_bend