{-# LANGUAGE MultilineStrings #-}

import Test

-- won't fix:
--
-- def main(x: Nat) -> Nat: x def = 5n def
-- is the same situation, is correct, and '=' is the first invalid token
-- the situation below won't occur in practice as 'let' isn't used anymore
-- unexpected_eq_ass_def :: String

unexpected_eq_ass_def = """
def main() -> Nat: foo def = 5n def
"""

main :: IO ()
main = testFile unexpected_eq_ass_def
  "use of def between variable and its assignment causes unexpected '='" $ \out err -> do
    assert (err `has` "PARSE_ERROR")
    assert (err `has` "unexpected '='")
