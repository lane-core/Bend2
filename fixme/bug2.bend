# this gives the error

  # PARSE_ERROR
  # Expected expression after assignment.
  #
  # At end of file.

# but it should be quivalent to the error when we use parenthesis around f(A):

  # def f(a : Set) -> Set:
  #   Bool
  # def g : ∀A: Set . (f(A)) =
  #   ()
  # 
  # ✓ f
  # ✗ g
  # Mismatch:
  # - Goal: ∀A:Set. Bool
  # - Type: Unit
  # Context:
  #
  # Location: (line 25, column 3)
  # 25 |   ()


def f(a : Set) -> Set:
  Bool

def g: ∀A: Set. f(A) =
  ()

# def g : ∀A: Set . (f(A)) =
#   ()

  
