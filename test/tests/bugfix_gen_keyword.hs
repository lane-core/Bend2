{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit b7315b6691f00dae6e78a5e0c2229d15d74b2876
--
-- bug description:
-- parser allows to do define gen(), while gen is a keyword
-- notice the error is not at the definition of gen() as it should, but in main
--
--   PARSE_ERROR
--   unexpected '('
--   expecting letter or underscore
--
--   At line 11, column 6:
--   11 |   gen()

gen_keyword :: String
gen_keyword = """
def gen() -> Nat:
  0n

def main() -> Nat:
  123
"""

main :: IO ()
main = testFile gen_keyword
  "defining a function called `gen` should trigger reserved keyword" $ \out err -> do
    assert (err `has` "PARSE_ERROR")
    assert (err `has` "reserved keyword 'gen'")
