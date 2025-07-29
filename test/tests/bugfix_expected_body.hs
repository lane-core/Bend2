{-# LANGUAGE MultilineStrings #-}

-- fixed in commit c3b02530dc9da4cae660da2e32e067a053ffea66
--
--
-- bug description:
--
-- this gives the error:
--
--   PARSE_ERROR
--   reserved keyword 'def'
--
--   At line 3, column 1:
--   3 | def main() -> Unit:
--       ^(marked here with color)
--
-- it would be more helpful if there was
-- a pointer to f, where the bug is actually address

import Test

expected_body :: String
expected_body = """
def f(x: Nat) -> Unit:

def main() -> Unit:
  ()
"""

main :: IO ()
main = testFile expected_body
  "writing a function with an empty body causes an expected body error" $ \out err -> do
    assert (err `has` "PARSE_ERROR")
    assert (err `has` "Expected body")
