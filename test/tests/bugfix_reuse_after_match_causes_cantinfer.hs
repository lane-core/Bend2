{-# LANGUAGE MultilineStrings #-}

-- fixed in commit (BenGen-align branch) 1bd511883460459183437dfafe71f7da1e3200cf

-- bug description:
-- reuse of matched variable causes can't infer
--
-- ✗ id
-- CantInfer:
-- Context:
-- - a : Nat
-- Location: (line 2, column 3)
-- 2 |   match a:
-- 3 |     case 0n:
-- 4 |       a # doesn't fail with 0n here
-- 5 |     case 1n+p:
-- 6 |       1n+p

import Test

reuse_after_match_causes_cantinfer :: String
reuse_after_match_causes_cantinfer = """
def id(a:Nat) -> Nat:
  match a:
    case 0n:
      a # doesn't fail with 0n here
    case 1n+p:
      1n+p
"""

main :: IO ()
main = testFileChecks reuse_after_match_causes_cantinfer
