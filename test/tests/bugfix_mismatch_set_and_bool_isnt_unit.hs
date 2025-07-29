{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit 0f280c12444431e03c6a715d3fffeeaf1c5ac2aa
--
-- bug description:
-- this gives the error
--
--   PARSE_ERROR
--   Expected expression after assignment.
--
--   At end of file.
--
-- but it should be quivalent to the error when we use parenthesis around f(A):
--
--   def f(a : Set) -> Set:
--     Bool
--   def g : ∀A: Set . (f(A)) =
--     ()
--
--   ✓ f
--   ✗ g
--   Mismatch:
--   - Goal: ∀A:Set. Bool
--   - Type: Unit
--   Context:
--
--   Location: (line 25, column 3)
--   25 |   ()

set_and_bool_isnt_unit :: String
set_and_bool_isnt_unit = """
def f(a : Set) -> Set:
  Bool

def g: ∀A: Set. f(A) =
  ()
"""

main :: IO ()
main = testFile set_and_bool_isnt_unit
  "using unit where a Σa:Set.Bool is expected causes a type mismatch" $ \out err -> do
    assert (err `has` "Mismatch:")
    assert (err `has` "Goal: ∀A:Set. Bool")
    assert (err `has` "Type: Unit")
