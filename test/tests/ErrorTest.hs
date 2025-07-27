{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main : Nat = True
"""

main :: IO ()
main = testFile main_bend
  "Should report a type mismatch error when assigning Bool to Nat." $ \out err -> do
    assert (out `has` "Mismatch:")
    assert (out `has` "Goal: Nat")
    assert (out `has` "Type: Bool")
