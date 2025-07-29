{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit (BendGen-align branch) 1f894d60578461a514bf9dacc3fc52ee6ac3e121
--
-- bug description:
-- this gives an unhelpful error, that doesn't show Goal/Type
-- or any other description of what the mismatch means
--
-- ✗ cong
--   Mismatch:
--   - f(x)
--   - f(y)
--   Context:
--   - A : Set
--   - B : Set
--   - f : A -> B
--   - x : A
--   - y : A
--   - h : A{x==y}
--   Location: (line 2, column 3)
--   2 |   finally

mismatch_cong :: String
mismatch_cong = """
def cong(A: Set, B: Set, f: (A -> B), x: A, y: A, h: A{x==y}) -> B{f(x)==f(y)}:
  finally
"""

main :: IO ()
main = testFileChecks mismatch_cong
