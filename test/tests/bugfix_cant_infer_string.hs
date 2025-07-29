{-# LANGUAGE MultilineStrings #-}

import Test

cant_infer_string :: String
cant_infer_string = """
def main() -> Char[]:
  x = "x"
  x
"""

main :: IO ()
main = testFileChecks cant_infer_string
