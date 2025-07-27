{-# LANGUAGE MultilineStrings #-}

import Test

cong_bend :: String
cong_bend = """
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  rewrite e
  {==}
"""

main :: IO ()
main = testFileChecks cong_bend
