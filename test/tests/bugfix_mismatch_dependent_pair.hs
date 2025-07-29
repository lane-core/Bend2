{-# LANGUAGE MultilineStrings #-}

-- fixed in commit (BendGen-align branch) 792244b7e400df3d774a44e20516d6d73d3baac6

-- bug description:
-- this should check bug gives:
--
-- ✗ f
-- Mismatch:
-- - Goal: ΣBool. λ{False:Unit;True:Nat}
-- - Type: Bool & Nat
-- Context:
--
-- Location: (line 2, column 3)
-- 2 |   (True,0n)

import Test

mismatch_dependent_pair :: String
mismatch_dependent_pair = """
def f() -> Σa:Bool. λ{False: Unit; True: Nat}(a):
  (True,0n)
"""

main :: IO ()
main = testFileChecks mismatch_dependent_pair
