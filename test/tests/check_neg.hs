{-# LANGUAGE MultilineStrings #-}

import Test

neg_bend :: String
neg_bend = """
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def T0 : Bool{False == neg(True)} = {==}
def T1 : Bool{True == neg(False)} = {==}
def T2 : Bool{neg(neg(True)) == True} = {==}
def T3 : Bool{neg(neg(False)) == False} = {==}
"""

main :: IO ()
main = testFileChecks neg_bend