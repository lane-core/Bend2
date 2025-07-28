{-# LANGUAGE MultilineStrings #-}

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
