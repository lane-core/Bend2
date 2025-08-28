{-# LANGUAGE MultilineStrings #-}

import Test

-- Negative Tests: Scoping and Binding Errors
-- These tests verify that our scoping rules are enforced correctly
negative_scoping_errors_bend :: String
negative_scoping_errors_bend = """
# Variable not in scope
def out_of_scope() -> Nat:
  x = 42n;
  y  # y is not defined

# Variable used before definition (forward reference)
def forward_reference() -> Nat:
  x = y + 1n;
  y = 42n;
  x

# Lambda variable escaping scope
def escaping_lambda() -> Nat -> Nat:
  f = lambda x. x + 1n;
  x  # x from lambda should not be in scope here

# Shadowing with different types (should cause confusion)
def type_shadowing() -> Nat:
  x = True;
  x = 42n;  # Redefining with different type
  x

# Using function name as variable
def recursive_name_clash() -> Nat:
  recursive_name_clash = 42n;  # Can't redefine function name
  recursive_name_clash
"""

-- Test that expects scoping errors
main :: IO ()
main = do
  result <- testFile negative_scoping_errors_bend
  case result of
    (_, _, err) | any (`elem` words err) ["NotInScope", "CantInfer", "ERROR", "PARSE_ERROR"] -> 
      putStrLn "✓ Scoping errors correctly detected"
    _ -> do
      putStrLn "✗ Expected scoping error but test passed"
      putStrLn $ "Error output: " ++ show result