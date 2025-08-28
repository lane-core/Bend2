{-# LANGUAGE MultilineStrings #-}

import Test

-- Well-formed Term Judgment Tests for Intrinsic Type System
-- Validates that only well-typed terms can be constructed and evaluated
nbe_wellformed_terms_bend :: String
nbe_wellformed_terms_bend = """
# Well-formed Term Judgment Validation Tests

# ============================================================================
# SECTION 1: TYPE SYSTEM CONSISTENCY TESTS
# ============================================================================

# Universe hierarchy consistency
def type_in_type_test() -> Set:
  Set  # Set : Set (Type-in-Type for practical programming)

def nested_universe_test() -> Set:
  Set  # Should be well-formed

# ============================================================================
# SECTION 2: DEPENDENT TYPE FORMATION RULES
# ============================================================================

# Pi-type formation (function types)
def pi_formation_test<A, B>() -> Set:
  A -> B

# Sigma-type formation (dependent pairs)
def sigma_formation_test<A, B>() -> Set:
  (A * B)

# Application well-formedness
def app_wellformed<A, B>(f: A -> B, x: A) -> B:
  return f(x)

# ============================================================================
# SECTION 3: LAMBDA ABSTRACTION AND BETA REDUCTION
# ============================================================================

# Lambda abstraction well-formedness
def lambda_wellformed<A, B>(body: A -> B) -> A -> B:
  lambda x. body(x)

# Beta reduction preservation
def beta_reduction_test<A>(f: A -> A, x: A) -> A:
  (lambda y. f(y))(x)  # Should reduce to f(x)

# Eta conversion test
def eta_conversion_test<A, B>(f: A -> B) -> A -> B:
  lambda x. f(x)  # Should be eta-equivalent to f

# ============================================================================
# SECTION 4: PATTERN MATCHING WELL-FORMEDNESS
# ============================================================================

# Exhaustive pattern matching on Bool
def bool_exhaustive(b: Bool) -> Nat:
  match b:
    case True:
      1n
    case False:
      0n

# Exhaustive pattern matching on Nat
def nat_pattern_wellformed(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + pred:
      1n + nat_pattern_wellformed(pred)

# List pattern matching with proper typing
def list_pattern_wellformed<A>(xs: [A]) -> Nat:
  match xs:
    case []:
      0n
    case h <> t:
      1n + list_pattern_wellformed<A>(t)

# ============================================================================
# SECTION 5: RECURSIVE FUNCTION WELL-FORMEDNESS
# ============================================================================

# Structurally recursive function (should be well-formed)
def structural_recursion(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + pred:
      1n + structural_recursion(pred)

# Mutual recursion well-formedness
def mutual_even(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n + pred:
      mutual_odd(pred)

def mutual_odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False
    case 1n + pred:
      mutual_even(pred)

# ============================================================================
# SECTION 6: TYPE CONVERSION AND EQUALITY
# ============================================================================

# Definitional equality test
def def_equality_test(n: Nat) -> Nat:
  n + 0n  # Should be definitionally equal to n

# Type conversion test
def type_conversion_test<A>(x: A) -> A:
  x  # Identity should preserve types exactly

# Propositional equality formation - simplified
def prop_equality_test() -> Set:
  Nat  # Simplified for testing

# ============================================================================
# SECTION 7: INDUCTIVE TYPE WELL-FORMEDNESS
# ============================================================================

# Custom inductive type with proper formation rules
type WellFormed<A: Set>:
  case @Base:
    value: A
  case @Step:
    prev: WellFormed<A>
    transform: A -> A

def wellformed_fold<A, B>(
  base_case: A -> B,
  step_case: B -> (A -> A) -> B,
  wf: WellFormed<A>
) -> B:
  match wf:
    case @Base{value}:
      base_case(value)
    case @Step{prev, transform}:
      step_case(wellformed_fold<A, B>(base_case, step_case, prev))(transform)

# ============================================================================
# SECTION 8: HIGHER-ORDER FUNCTION TYPE PRESERVATION
# ============================================================================

# Map preserves list type structure
def map_wellformed<A, B>(f: A -> B, xs: [A]) -> [B]:
  match xs:
    case []:
      []
    case h <> t:
      f(h) <> map_wellformed<A, B>(f, t)

# Fold preserves type structure
def fold_wellformed<A, B>(f: B -> A -> B, acc: B, xs: [A]) -> B:
  match xs:
    case []:
      acc
    case h <> t:
      fold_wellformed<A, B>(f, f(acc)(h), t)

# Function composition preserves types
def compose_wellformed<A, B, C>(f: B -> C, g: A -> B, x: A) -> C:
  f(g(x))

# ============================================================================
# SECTION 9: DEPENDENT TYPE ELIMINATION
# ============================================================================

# Simplified dependent functions for testing
def dependent_app_test<A>(f: A -> A, a: A) -> A:
  f(a)

# Simplified pair projection
def dependent_fst<A, B>(pair: (A * B)) -> A:
  match pair:
    case (a, b):
      a

def dependent_snd<A, B>(pair: (A * B)) -> B:
  match pair:
    case (a, b):
      b

# ============================================================================
# SECTION 10: COMPREHENSIVE WELL-FORMEDNESS ASSERTIONS
# ============================================================================

# Test universe consistency
assert Set == type_in_type_test() : Set

# Test lambda and beta reduction
assert 42n == beta_reduction_test<Nat>(lambda x. x, 42n) : Nat
assert 10n == (lambda f. f(5n))(lambda x. x + 5n) : Nat

# Test pattern matching exhaustiveness
assert 1n == bool_exhaustive(True) : Nat
assert 0n == bool_exhaustive(False) : Nat
assert 5n == nat_pattern_wellformed(5n) : Nat
assert 3n == list_pattern_wellformed<Nat>([1n, 2n, 3n]) : Nat

# Test structural recursion
assert 10n == structural_recursion(10n) : Nat

# Test mutual recursion
assert True == mutual_even(4n) : Bool
assert False == mutual_even(3n) : Bool
assert True == mutual_odd(5n) : Bool
assert False == mutual_odd(6n) : Bool

# Test definitional equality
assert 42n == def_equality_test(42n) : Nat

# Test inductive type operations
assert 11n == wellformed_fold<Nat, Nat>(
  lambda x. x,
  lambda acc. lambda f. f(acc),
  @Step{@Step{@Base{5n}, lambda x. x * 2n}, lambda x. x + 1n}
) : Nat  # ((5 * 2) + 1) = 11

# Test higher-order function preservation
assert [2n, 4n, 6n] == map_wellformed<Nat, Nat>(lambda x. x * 2n, [1n, 2n, 3n]) : [Nat]
assert 10n == fold_wellformed<Nat, Nat>(lambda acc. lambda x. acc + x, 0n, [1n, 2n, 3n, 4n]) : Nat

# Test function composition type preservation
assert 14n == compose_wellformed<Nat, Nat, Nat>(lambda x. x + 1n, lambda x. x * 2n, 6n) : Nat

# Test dependent types
assert 5n == dependent_fst<Nat, Bool>((5n, True)) : Nat

# Complex nested type preservation test
def complex_nested_test<A>(xs: [[A]]) -> Nat:
  fold_wellformed<[A], Nat>(
    lambda acc. lambda ys. acc + list_pattern_wellformed<A>(ys),
    0n,
    xs
  )

assert 6n == complex_nested_test<Nat>([[1n, 2n], [3n], [4n, 5n, 6n]]) : Nat

# Type-level computation preservation
def type_computation_test(n: Nat) -> [Nat]:
  match n:
    case 0n:
      []
    case 1n + pred:
      n <> type_computation_test(pred)

assert [3n, 2n, 1n] == type_computation_test(3n) : [Nat]
"""

main :: IO ()
main = testFileChecks nbe_wellformed_terms_bend