{-# LANGUAGE MultilineStrings #-}

import Test

bool_isnt_nat_bend :: String
bool_isnt_nat_bend = """
def main : Nat = True
"""

main :: IO ()
main = testFile bool_isnt_nat_bend
  "using bool where a nat is expected causes a type mismatch" $ \out err -> do
    assert (err `has` "Mismatch:")
    assert (err `has` "Goal: Nat")
    assert (err `has` "Type: Bool")
