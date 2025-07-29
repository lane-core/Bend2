{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- This was giving a parse error unless parenthesizing the second Nat
--   PARSE_ERROR
--  unexpected 'N'
--  expecting pair
-- 
--  At line 1, column 19:
--  1 | def f() -> Nat & Nat:
--                       ^ (color marker points here)


pair_type_sugar_parsing :: String
pair_type_sugar_parsing = """
def f() -> Nat & Nat:
  (0n,1n)
"""

main :: IO ()
main = testFileChecks pair_type_sugar_parsing
