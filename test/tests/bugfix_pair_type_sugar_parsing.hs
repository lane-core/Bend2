{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit 91c8924cffc7f476c8925fffb7e10bf1642be5b3
--
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
