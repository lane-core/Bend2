{-# LANGUAGE MultilineStrings #-}

import Test

-- Simple, definitive type errors that should definitely fail
negative_simple_type_errors_bend :: String
negative_simple_type_errors_bend = """
# Clear Bool/Nat mismatch in addition
def bool_nat_add() -> Nat:
  True + 1n

# Using Bool as function
def bool_as_function() -> Nat:
  True(42n)

# Wrong list type
def wrong_list_type() -> [Bool]:
  [1n, 2n, 3n]
"""

main :: IO ()
main = testFile negative_simple_type_errors_bend "simple type errors should fail" $ \out err -> do
  if any (`elem` words err) ["ERROR", "CantInfer", "Mismatch", "PARSE_ERROR", "expected", "Type"]
    then putStrLn "✅ Simple type errors correctly detected"
    else error $ "❌ Expected type error but got: out='" ++ out ++ "' err='" ++ err ++ "'"