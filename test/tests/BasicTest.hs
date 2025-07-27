{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main : Nat = 1n + 3n
"""

main :: IO ()
main = testFile main_bend
  "Should compute addition and print Nat literals correctly." $ \out err -> do
    assert (out `has` "4n")
