{-# LANGUAGE MultilineStrings #-}

import Test

-- Definite errors that must fail
negative_definite_errors_bend :: String
negative_definite_errors_bend = """
# Undefined variable - this MUST fail
def undefined_variable_test() -> Nat:
  some_undefined_variable

# Invalid syntax - incomplete expression
def incomplete_expr() -> Nat:
  1n +

# Non-existent constructor - this should fail
def nonexistent_constructor() -> Nat:
  @NonExistentConstructor{42n}
"""

main :: IO ()
main = testFile negative_definite_errors_bend "definite errors must fail" $ \out err -> do
  putStrLn $ "Debug - out: '" ++ out ++ "'"
  putStrLn $ "Debug - err: '" ++ err ++ "'"
  if err /= "" && any (`elem` words err) ["ERROR", "CantInfer", "Mismatch", "PARSE_ERROR", "Expected", "NotInScope"]
    then putStrLn "✅ Definite errors correctly detected"
    else error $ "❌ Expected definite error but passed!"