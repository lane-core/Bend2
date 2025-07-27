{-# LANGUAGE MultilineStrings #-}

import Test

double_neg_identity_goal_0_bend :: String
double_neg_identity_goal_0_bend = """
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def double_neg_identity(x: Bool) -> Bool{neg(neg(x)) == x}:
  if x:
    ()
  else:
    {==}
"""

main :: IO ()
main = testFileGoal double_neg_identity_goal_0_bend "Bool{True==True}" []