{-# LANGUAGE MultilineStrings #-}

-- fixed in commit (BendGen-align branch) d7400808f1a0176427d94fe3a68193b78cd52d75

-- bug description:
-- this should check bug gives can't infer due to unused var:
--
-- ✗ t
-- CantInfer:
-- Context:
-- - A : Set
-- - e : Empty
-- - unused : Nat
-- Location: (line 3, column 3)

import Test

unused_blocks_infer :: String
unused_blocks_infer = """
def t(A:Set, e:Empty) -> A:
  unused = 3n
  λ{}(e)
"""

main :: IO ()
main = testFileChecks unused_blocks_infer
