# Bend Test Framework

This directory contains a minimal testing framework for Bend.

## Running Tests

Run all tests:
```bash
cabal test
```

Run a single test (several options):
```bash
# Direct approach
runhaskell -i:test test/tests/BasicTest.hs

# Using cabal exec (runs in cabal environment)
cabal exec -- runhaskell -i:test test/tests/BasicTest.hs

# Using cabal repl (interactive)
cabal repl test:bend-test
> :load test/tests/BasicTest.hs
> main
```

## Writing Tests

Create test files in `test/tests/` with the `.hs` extension. Each test file should:

1. Enable MultilineStrings: `{-# LANGUAGE MultilineStrings #-}`
2. Import the `Test` module
3. Define a `main :: IO ()` function
4. Use `testFile` to test single Bend files

### Example Test

```haskell
{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main : Nat = 1n + 3n
"""

main :: IO ()
main = testFile main_bend
  "Should compute addition and print Nat literals correctly." $ \out err -> do
    assert (out `has` "4n")
```

## API Reference

### Core Testing Functions

```haskell
-- Test with multiple files
test :: String -> [(String, String)] -> String -> (String -> String -> IO ()) -> IO ()

-- Test a single Bend file
testFile :: String -> String -> (String -> String -> IO ()) -> IO ()
```

### Assertions

```haskell
-- Basic assertion
assert :: Bool -> IO ()

-- Check if output contains expected text (handles ANSI colors automatically)
has :: String -> String -> Bool

-- Usage examples:
assert (output `has` "expected text")
assert (x == y)
assert (length items > 0)
```

## Test Output

Tests display:
- Test name in bold: `> TestName`
- Optional description in gray
- Bend command output indented with colored `>` symbols (green for passing, red for failing)
- Summary of passed/failed tests