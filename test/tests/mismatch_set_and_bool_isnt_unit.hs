{-# LANGUAGE MultilineStrings #-}

import Test

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
