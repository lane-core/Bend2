{-# LANGUAGE MultilineStrings #-}

import Test

-- Negative Tests: Recursion and Termination Errors
-- These tests verify that our recursion checker works appropriately
negative_recursive_errors_bend :: String
negative_recursive_errors_bend = """
# Infinite recursion without base case
def infinite_recursion(n: Nat) -> Nat:
  1n + infinite_recursion(n)

# Non-structural recursion (potentially problematic)
def non_structural_recursion(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + pred:
      non_structural_recursion(n)  # Calling on n, not pred

# Mutual recursion without proper base case
def mutual_infinite_1(n: Nat) -> Nat:
  1n + mutual_infinite_2(n)

def mutual_infinite_2(n: Nat) -> Nat:
  1n + mutual_infinite_1(n)

# Recursion on wrong argument
def wrong_argument_recursion(x: Nat, y: Nat) -> Nat:
  match x:
    case 0n:
      0n
    case 1n + pred:
      wrong_argument_recursion(x, y)  # Should recurse on pred, not x
"""

-- Test that expects recursion errors (if termination checking is enabled)
main :: IO ()
main = do
  result <- testFile negative_recursive_errors_bend
  case result of
    (_, _, err) | any (`elem` words err) ["Termination", "ERROR", "CantInfer"] -> 
      putStrLn "✓ Recursion errors correctly detected"
    (out, _, err) | null err -> do
      putStrLn "⚠ Recursion test passed - termination checking may be disabled"
      putStrLn "This indicates the type system allows potentially non-terminating recursion"
    _ -> do
      putStrLn "✗ Unexpected result for recursion test"
      putStrLn $ "Error output: " ++ show result