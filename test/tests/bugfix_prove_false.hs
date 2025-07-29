{-# LANGUAGE MultilineStrings #-}

-- bug description:
--  while we don't have a termination checker we can prove absurdity in bend
--  this checks, although it never halts
-- ✓ absurdity
-- ✓ main
-- It also suffices just to write:
-- def main() -> Empty: main()


import Test

prove_false :: String
prove_false = """
def absurdity(A: Set) -> A:
  absurdity(A)

def main() -> Empty:
  absurdity(Empty)
"""

main :: IO ()
main = testFileWithTimeout prove_false
  "Proving False should not be allowed" (\out err -> do
    assert (err `has` "Mismatch")
    assert (not (err == ""))) 3

