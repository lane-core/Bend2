{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/17
--

cant_infer_string :: String
cant_infer_string = """
def main() -> Char[]:
  x = "x"
  x
"""

main :: IO ()
main = testFileChecks cant_infer_string
