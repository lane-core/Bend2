{-# LANGUAGE MultilineStrings #-}

import Test

neg_bend :: String
neg_bend = """
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

assert False == neg(True) : Bool
assert True == neg(False) : Bool
assert neg(neg(True)) == True : Bool
assert neg(neg(False)) == False : Bool
"""

main :: IO ()
main = testFileChecks neg_bend