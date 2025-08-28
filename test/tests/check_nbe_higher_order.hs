{-# LANGUAGE MultilineStrings #-}

import Test

-- Test higher-order functions and function composition for NbE
nbe_higher_order_bend :: String
nbe_higher_order_bend = """
# Higher-order function composition
def compose<A,B,C>(f: B -> C, g: A -> B, x: A) -> C:
  f(g(x))

# Function application utility
def apply<A,B>(f: A -> B, x: A) -> B:
  f(x)

# Apply function twice
def apply_twice<A>(f: A -> A, x: A) -> A:
  f(f(x))

# Curried addition
def add_curry(x: Nat) -> (Nat -> Nat):
  lambda y. x + y

# Basic arithmetic functions for testing
def double(x: Nat) -> Nat:
  x * 2n

def square(x: Nat) -> Nat:
  x * x

def add_five(x: Nat) -> Nat:
  x + 5n

def inc(x: Nat) -> Nat:
  x + 1n

# Complex nested computation
def nested_ops(x: Nat) -> Nat:
  compose<Nat,Nat,Nat>(double, add_five, x)

# Test basic function composition
assert 14n == compose<Nat,Nat,Nat>(double, add_five, 2n) : Nat
assert 18n == compose<Nat,Nat,Nat>(add_five, double, 4n) : Nat

# Test function application
assert 10n == apply<Nat,Nat>(double, 5n) : Nat
assert 25n == apply<Nat,Nat>(square, 5n) : Nat

# Test apply twice
assert 8n == apply_twice<Nat>(double, 2n) : Nat
assert 7n == apply_twice<Nat>(inc, 5n) : Nat

# Test curried addition
assert 8n == add_curry(3n)(5n) : Nat
assert 12n == add_curry(7n)(5n) : Nat

# Test nested operations
assert 14n == nested_ops(2n) : Nat

# Test multiple compositions
assert 22n == compose<Nat,Nat,Nat>(add_five, compose<Nat,Nat,Nat>(double, add_five, 3n), 0n) : Nat
"""

main :: IO ()
main = testFileChecks nbe_higher_order_bend