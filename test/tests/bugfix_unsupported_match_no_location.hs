{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/9
--
-- suggested to just add location, but perhaps ideally we should say "Can't assign to Bool"

unsupported_match_no_location :: String
unsupported_match_no_location = """
def main() -> Nat:
  Bool = 3n;
  1n
"""

main :: IO ()
main = testFile unsupported_match_no_location
  "" $ \out err -> do
    assert (err `has` "Cannot assign a value to `Bool` native type")
    assert (err `has` "At")
