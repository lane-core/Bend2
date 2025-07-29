{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit 4bf7914a6c9f34d0d2b5e3c7c8fe04dadbf8642d
--
-- bug description:
-- Nat Op2 still missing, this gives error
--
--   ✗ f
--   Mismatch:
--   - Goal: Num
--   - Type: Nat
--   Context:
--   - a : Nat
--   - b : Nat
--   Location: (line 17, column 3)
--   17 |   a+b

nat_op2 :: String
nat_op2 = """
def f(a:Nat, b:Nat) -> Nat:
  a+b

def main : Nat = f(1n,2n)
"""

main :: IO ()
main = testFileChecks nat_op2
