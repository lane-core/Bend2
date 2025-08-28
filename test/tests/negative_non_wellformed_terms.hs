{-# LANGUAGE MultilineStrings #-}

import Test

-- Negative Tests: Non-Well-Formed Terms
-- These tests verify that our intrinsic type system rejects invalid constructions
negative_non_wellformed_terms_bend :: String
negative_non_wellformed_terms_bend = """
# Undefined variable reference
def undefined_variable() -> Nat:
  undefined_var

# Invalid pattern match: non-exhaustive
def non_exhaustive_match(b: Bool) -> Nat:
  match b:
    case True:
      1n
    # Missing False case

# Invalid constructor application
def invalid_constructor() -> Nat:
  @Some{1n, 2n}  # Some only takes one argument

# Infinite type (if detected)
def infinite_type() -> Nat:
  lambda f. f(f)

# Wrong arity function application
def wrong_arity() -> Nat:
  (lambda x. lambda y. x + y)(1n)  # Partial application should be fine, but wrong usage
"""

-- Test that expects well-formedness errors
main :: IO ()
main = testFile negative_non_wellformed_terms_bend "should fail with well-formedness error" $ \out err -> do
  if any (`elem` words err) ["CantInfer", "NotInScope", "Mismatch", "ERROR", "PARSE_ERROR"]
    then putStrLn "✅ Non-well-formed terms correctly detected"
    else error "❌ Expected well-formedness error but test passed"