{-# LANGUAGE MultilineStrings #-}

import Test


-- fixed in commit df355af377ca90afe8f2739e4f2d06b2d84992d2
--
-- an unused variable causes a type mismatch by rewriting goal:

unused_var_mismatch_rewriting :: String
unused_var_mismatch_rewriting = """
def thm(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  x = A
  unused_but_in_goal_1 = Σa:A.B
  unused_but_in_goal_2 = Σa:A.B
  λI.I(Σa:A.B, λa1.λb1.(a1,b1))

  # old error:
  # ✗ thm
  # Mismatch:
  # - Goal: unused_but_in_goal
  # - Type: A & B
  # Context:
  # - A : Set
  # - B : Set
  # - unused_but_in_goal : Set
  # - I : ∀C:Set. (A -> B -> C) -> C
  # - a1 : A
  # - b1 : B
  # Location: (line 7, column 24)
  # 7 |   λI.I(Σa:A.B, λa1.λb1.(a1,b1))
"""

main :: IO ()
main = testFileChecks unused_var_mismatch_rewriting 
