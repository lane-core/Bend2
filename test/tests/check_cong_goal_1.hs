{-# LANGUAGE MultilineStrings #-}

import Test

cong_goal_1_bend :: String
cong_goal_1_bend = """
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  rewrite e
  ()
"""

main :: IO ()
main = testFileGoal cong_goal_1_bend "B{f(b)==f(b)}" [("A", "Set"), ("B", "Set"), ("a", "A"), ("b", "A"), ("f", "∀A. B"), ("e", "A{a==b}")]