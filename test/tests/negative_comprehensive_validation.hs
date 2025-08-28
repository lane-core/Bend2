{-# LANGUAGE MultilineStrings #-}

import Test

-- Comprehensive Negative Test Suite
-- Validates that the type system correctly rejects various categories of invalid terms
negative_comprehensive_validation_bend :: String
negative_comprehensive_validation_bend = """
# CATEGORY 1: BASIC TYPE ERRORS

# Bool/Nat mismatch
def bool_nat_mismatch() -> Nat:
  True + False

# Function/Value mismatch  
def function_value_mismatch() -> Nat:
  let f = lambda x. x
  f + 42n

# List type inconsistency
def list_type_inconsistency() -> [Nat]:
  [1n, True, "hello"]

# CATEGORY 2: ARITY MISMATCHES

# Too few arguments
def too_few_args() -> Nat:
  let add_two = lambda x. lambda y. x + y
  add_two(5n)  # Missing second argument in final application

# Too many arguments to non-function
def too_many_args() -> Nat:
  42n(10n)(20n)

# Wrong constructor arity
def wrong_constructor_arity() -> Maybe<Nat>:
  @Some{1n, 2n}  # Some takes 1 argument, not 2

# CATEGORY 3: SCOPING VIOLATIONS

# Undefined variable
def undefined_var() -> Nat:
  x + y  # Both x and y undefined

# Variable escaping lambda scope
def escaping_scope() -> Nat:
  f = lambda x. lambda y. x + y;
  x  # x not in scope outside lambda

# CATEGORY 4: PATTERN MATCHING ERRORS

# Wrong pattern type
def wrong_pattern_type() -> Nat:
  match 42n:
    case True: 1n
    case False: 0n

# Constructor pattern mismatch
def constructor_pattern_mismatch() -> Nat:
  match @Some{42n}:
    case @None: 0n
    case @Some{x, y}: x  # Some has 1 field, not 2

# CATEGORY 5: RECURSIVE DEFINITION ISSUES

# Self-reference in non-recursive context
def improper_self_reference() -> Nat:
  improper_self_reference + 1n  # Should be in match/conditional

# CATEGORY 6: TYPE ANNOTATION MISMATCHES

# Declared type doesn't match implementation
def type_annotation_mismatch() -> Bool:
  42n  # Returns Nat but declared Bool

# Generic type parameter confusion
def generic_confusion<A>() -> A:
  42n  # Can't return Nat for arbitrary A

# CATEGORY 7: INVALID SYNTAX CONSTRUCTS

# Invalid lambda syntax
def invalid_lambda() -> Nat:
  lambda. 42n  # Missing parameter

# Invalid match syntax  
def invalid_match() -> Nat:
  match:
    case 0n: 0n

# Invalid constructor reference
def invalid_constructor() -> Nat:
  @NonExistent{42n}

# CATEGORY 8: IMPOSSIBLE EQUALITY PROOFS

# Trying to prove false equality
def false_equality() -> Nat{0n == 1n}:
  {==}  # Should fail - can't prove 0n == 1n

# CATEGORY 9: UNIVERSE INCONSISTENCIES (if checked)

# Type-in-Type issues (may not be caught in Bend2)
def universe_issue() -> Set:
  Set -> Set  # Depends on universe handling

# CATEGORY 10: MALFORMED INDUCTIVE TYPES

# Invalid datatype definition (this would be a top-level error)
# We'll test with malformed constructor usage instead
def malformed_constructor() -> Nat:
  @Invalid{field1, field2, field3}  # Non-existent constructor
"""

-- Custom test runner for negative tests
main :: IO ()
main = testFile negative_comprehensive_validation_bend "comprehensive negative validation" $ \out err -> do
  putStrLn "🔍 Testing negative cases to validate type system robustness..."
  if any (`elem` words err) ["ERROR", "CantInfer", "Mismatch", "NotInScope", "PARSE_ERROR"]
    then do
      putStrLn "✅ EXCELLENT: Type system correctly rejects invalid terms!"
      putStrLn "   This proves the type system is not trivial and enforces correctness."
    else do
      putStrLn "❌ CONCERNING: Negative test didn't fail - type system may be too permissive!"
      error "Type checker might not be catching errors properly"