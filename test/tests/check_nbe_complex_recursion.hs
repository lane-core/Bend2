{-# LANGUAGE MultilineStrings #-}

import Test

-- Test complex recursive patterns and deep evaluation for NbE
nbe_complex_recursion_bend :: String
nbe_complex_recursion_bend = """
# Factorial with accumulator (tail recursion)
def factorial_acc(n: Nat, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n + pred:
      factorial_acc(pred, acc * n)

def factorial(n: Nat) -> Nat:
  factorial_acc(n, 1n)

# Fibonacci with helper function
def fib_helper(n: Nat, a: Nat, b: Nat) -> Nat:
  match n:
    case 0n:
      a
    case 1n + pred:
      fib_helper(pred, b, a + b)

def fibonacci(n: Nat) -> Nat:
  fib_helper(n, 0n, 1n)

# Complex list operations
def list_length<A>(xs: A[]) -> Nat:
  match xs:
    case []:
      0n
    case x <> rest:
      1n + list_length<A>(rest)

def list_sum(xs: Nat[]) -> Nat:
  match xs:
    case []:
      0n
    case x <> rest:
      x + list_sum(rest)

def list_reverse_acc<A>(xs: A[], acc: A[]) -> A[]:
  match xs:
    case []:
      acc
    case x <> rest:
      list_reverse_acc<A>(rest, x <> acc)

def list_reverse<A>(xs: A[]) -> A[]:
  list_reverse_acc<A>(xs, [])

# Power function (recursive)
def power(base: Nat, exp: Nat) -> Nat:
  match exp:
    case 0n:
      1n
    case 1n + pred:
      base * power(base, pred)

# Mutual recursion - even/odd
def is_even(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n + pred:
      is_odd(pred)

def is_odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False
    case 1n + pred:
      is_even(pred)

# Test factorial
assert 1n == factorial(0n) : Nat
assert 1n == factorial(1n) : Nat
assert 6n == factorial(3n) : Nat
assert 24n == factorial(4n) : Nat

# Test fibonacci
assert 0n == fibonacci(0n) : Nat
assert 1n == fibonacci(1n) : Nat
assert 1n == fibonacci(2n) : Nat
assert 2n == fibonacci(3n) : Nat
assert 8n == fibonacci(6n) : Nat

# Test list operations
assert 3n == list_length<Nat>([1n, 2n, 3n]) : Nat
assert 0n == list_length<Nat>([]) : Nat
assert 10n == list_sum([1n, 2n, 3n, 4n]) : Nat
assert [3n, 2n, 1n] == list_reverse<Nat>([1n, 2n, 3n]) : Nat[]

# Test power function
assert 1n == power(5n, 0n) : Nat
assert 8n == power(2n, 3n) : Nat
assert 25n == power(5n, 2n) : Nat

# Test mutual recursion
assert True == is_even(0n) : Bool
assert False == is_even(1n) : Bool
assert True == is_even(4n) : Bool
assert False == is_odd(0n) : Bool
assert True == is_odd(1n) : Bool
assert False == is_odd(4n) : Bool
"""

main :: IO ()
main = testFileChecks nbe_complex_recursion_bend