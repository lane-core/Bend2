{-# LANGUAGE MultilineStrings #-}

import Test

-- Negative Tests: Pattern Matching Errors
-- These tests verify that our pattern matcher correctly rejects invalid patterns
negative_pattern_matching_errors_bend :: String
negative_pattern_matching_errors_bend = """
# Invalid pattern: wrong constructor arity
def wrong_constructor_arity() -> Nat:
  match @Some{42n}:
    case @Some{x, y}:  # Some only has one field
      x

# Invalid pattern: type mismatch in pattern
def pattern_type_mismatch() -> Nat:
  match [1n, 2n, 3n]:
    case True:  # Bool pattern on Nat list
      1n
    case False:
      0n

# Invalid pattern: overlapping/unreachable patterns
def unreachable_pattern(n: Nat) -> Nat:
  match n:
    case 1n + x:
      x
    case 5n:  # This should be unreachable since 5n matches 1n+4n
      0n
    case 0n:
      0n

# Invalid pattern: non-linear pattern (same variable twice)
def non_linear_pattern() -> Nat:
  match (1n, 2n):
    case (x, x):  # Same variable used twice
      x
"""

-- Test that expects pattern matching errors
main :: IO ()
main = do
  result <- testFile negative_pattern_matching_errors_bend
  case result of
    (_, _, err) | any (`elem` words err) ["PARSE_ERROR", "CantInfer", "Mismatch", "ERROR"] -> 
      putStrLn "✓ Pattern matching errors correctly detected"
    _ -> do
      putStrLn "✗ Expected pattern matching error but test passed"
      putStrLn $ "Error output: " ++ show result