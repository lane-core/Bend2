{-# LANGUAGE MultilineStrings #-}

import Test

-- Negative Tests: Syntax Errors
-- These tests verify that our parser correctly rejects malformed syntax
negative_syntax_errors_bend :: String
negative_syntax_errors_bend = """
# These should all cause PARSE_ERROR

# Missing function body
def incomplete_function() -> Nat:

# Invalid identifier starting with digit
def 1invalid_name() -> Nat:
  42n

# Missing type annotation
def missing_type():
  42n
"""

-- Test that expects a parse error
main :: IO ()
main = testFile negative_syntax_errors_bend "should fail with syntax error" $ \out err -> do
  if any (`elem` words err) ["PARSE_ERROR", "Expected"]
    then putStrLn "✅ Syntax errors correctly detected"
    else error "❌ Expected parse error but test passed"