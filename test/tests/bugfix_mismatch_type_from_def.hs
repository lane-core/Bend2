{-# LANGUAGE MultilineStrings #-}

-- fixed in commit (BenGen-align branch) 1f894d60578461a514bf9dacc3fc52ee6ac3e121

-- bug description:
-- this should check but thm_1 fails
--
-- ✓ Falso
-- ✗ thm_1
-- Mismatch:
-- - Goal: _ -> _
-- - Type: ∀P:Set. P
-- Context:
-- - F : ∀P:Set. P
-- Location: (line 5, column 6)
-- 5 |   λF.F(Empty)
--
-- ✓ thm_2

import Test

mismatch_type_from_def :: String
mismatch_type_from_def = """
def Falso() -> Set:
  ∀P:Set.P
def thm_1() -> Falso -> Empty:
  λF.F(Empty)

def thm_2() ->  (∀P:Set.P) -> Empty:
  λF.F(Empty)
"""

main :: IO ()
main = testFileChecks mismatch_type_from_def
