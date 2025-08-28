{-# LANGUAGE MultilineStrings #-}

import Test

-- Test let expression substitution and normalization for NbE
nbe_let_substitution_bend :: String
nbe_let_substitution_bend = """
# Complex let expression chains
def complex_computation(x: Nat) -> Nat:
  a = x + 1n
  b = a * 2n
  c_val = b + 3n
  d = c_val * c_val
  e = d - 5n
  e

# Nested let expressions
def nested_computation() -> Nat:
  outer = 
    inner1 = 3n + 4n
    inner2 = inner1 * 2n
    inner2 + 1n
  result = outer * 2n
  result

# Let expressions with function calls
def let_with_calls(x: Nat) -> Nat:
  doubled = x * 2n
  squared = doubled * doubled
  result = squared + doubled
  result

# Complex substitution chains
def substitution_chain() -> Nat:
  f = 5n
  g = f + 3n
  h = g * f
  i = h + g + f
  i

# Let in pattern matching context
def let_in_match(xs: Nat[]) -> Nat:
  match xs:
    case []:
      default = 42n
      default
    case x <> rest:
      head_doubled = x * 2n
      tail_length = 1n  # Simplified to avoid nested match
      head_doubled + tail_length

# Recursive function with let expressions
def recursive_with_lets(n: Nat) -> Nat:
  match n:
    case 0n:
      base = 1n
      base
    case 1n + pred:
      prev_result = recursive_with_lets(pred)
      current_result = n + prev_result
      current_result

# Let with lambda expressions
def let_with_lambda() -> Nat:
  f = lambda x. x * 2n
  g = lambda y. y + 3n
  result = f(g(5n))
  result

# Multiple let bindings in sequence
def multiple_lets(x: Nat, y: Nat) -> Nat:
  a = x + y
  b = a * 2n
  c_val = b + 1n
  d = c_val * c_val
  final = d + a + b + c_val
  final

# Test complex computation
assert 67n == complex_computation(5n) : Nat
assert 23n == complex_computation(2n) : Nat

# Test nested computation
assert 30n == nested_computation() : Nat

# Test let with function calls
assert 180n == let_with_calls(6n) : Nat

# Test substitution chain
assert 53n == substitution_chain() : Nat

# Test let in match
assert 42n == let_in_match([]) : Nat
assert 11n == let_in_match([5n, 8n]) : Nat

# Test recursive with lets
assert 1n == recursive_with_lets(0n) : Nat
assert 4n == recursive_with_lets(2n) : Nat
assert 10n == recursive_with_lets(4n) : Nat

# Test let with lambda
assert 16n == let_with_lambda() : Nat

# Test multiple lets
assert 120n == multiple_lets(3n, 4n) : Nat
"""

main :: IO ()
main = testFileChecks nbe_let_substitution_bend