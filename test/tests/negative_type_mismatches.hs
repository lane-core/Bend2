{-# LANGUAGE MultilineStrings #-}

import Test

-- Negative Tests: Type Mismatches 
-- These tests verify that our type checker correctly rejects type errors
negative_type_mismatches_bend :: String
negative_type_mismatches_bend = """
# Type mismatch: using Bool where Nat expected
def type_mismatch_bool_nat() -> Nat:
  True

# Type mismatch: wrong function argument type
def wrong_arg_type() -> Nat:
  id<Nat>(True)

# Type mismatch: inconsistent list types
def inconsistent_list() -> [Nat]:
  [1n, True, 3n]

# Type mismatch: applying non-function
def apply_non_function() -> Nat:
  42n(10n)

# Type mismatch: wrong return type in match
def wrong_match_return() -> Bool:
  match True:
    case True:
      42n
    case False:
      False
"""

-- Test that expects a type error
main :: IO ()
main = testFile negative_type_mismatches_bend "should fail with type error" $ \out err -> do
  if any (`elem` words err) ["TYPE_ERROR", "CantInfer", "Mismatch", "ERROR"]
    then putStrLn "✅ Type mismatches correctly detected"
    else error "❌ Expected type error but test passed"