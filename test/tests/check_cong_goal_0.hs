{-# LANGUAGE MultilineStrings #-}

import Test

cong_goal_0_bend :: String
cong_goal_0_bend = """
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  ()
"""

main :: IO ()
main = testFileGoal cong_goal_0_bend "B{f(a)==f(b)}" []
