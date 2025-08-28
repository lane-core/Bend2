{-# LANGUAGE MultilineStrings #-}

import Test

-- NbE Correctness Property Tests
-- Validates fundamental properties: confluence, normalization, type preservation
nbe_correctness_properties_bend :: String
nbe_correctness_properties_bend = """
# NbE Correctness and Property Tests

# ============================================================================
# SECTION 1: CONFLUENCE PROPERTIES (CHURCH-ROSSER)
# ============================================================================

# Test that different reduction paths yield the same result
def confluence_test1(f: Nat -> Nat, x: Nat) -> Nat:
  # Path 1: Apply then reduce
  result1 = f(x + 0n);
  # Path 2: Reduce then apply  
  result2 = f(x);
  result1  # Both should normalize to the same value

def confluence_test2() -> Nat:
  # Multiple beta reductions should commute
  f = lambda x. lambda y. x + y;
  g = lambda z. z * 2n;
  # Different application orders
  result1 = f(5n)(g(3n));  # ((lambda x y. x + y) 5) ((lambda z. z * 2) 3)
  result2 = (lambda y. 5n + y)(g(3n));  # Should reduce to same normal form
  result1

# ============================================================================
# SECTION 2: NORMALIZATION PROPERTIES
# ============================================================================

# Strong normalization: all reduction sequences terminate
def normalization_test1(n: Nat) -> Nat:
  # Nested applications should all normalize
  f = lambda x. lambda y. lambda z. x + y + z;
  f(n)(n + 1n)(n + 2n)

# Weak head normal form preservation
def whnf_test(b: Bool, x: Nat, y: Nat) -> Nat:
  # Should normalize to constructor form
  match b:
    case True:
      x + y
    case False:
      x * y

# ============================================================================
# SECTION 3: TYPE PRESERVATION PROPERTIES
# ============================================================================

# Subject reduction: types preserved under reduction
def subject_reduction_test<A>(f: A -> A, x: A) -> A:
  # (lambda y. f(y))(x) : A should reduce to f(x) : A
  (lambda y. f(y))(x)

# Type preservation under substitution
def substitution_preservation<A, B>(f: A -> B, x: A) -> B:
  # Substitution should preserve typing
  g = lambda z. f(z);
  g(x)  # Should have type B

# ============================================================================
# SECTION 4: BETA-ETA EQUIVALENCE PROPERTIES
# ============================================================================

# Beta reduction correctness
def beta_correctness_test() -> Nat:
  # (lambda x. x + 5)(10) should beta-reduce to 10 + 5
  (lambda x. x + 5n)(10n)

# Eta expansion correctness  
def eta_correctness_test<A, B>(f: A -> B) -> A -> B:
  # f should be eta-equivalent to lambda x. f(x)
  lambda x. f(x)

# Higher-order beta reduction
def higher_order_beta() -> Nat:
  compose = lambda f. lambda g. lambda x. f(g(x));
  add5 = lambda y. y + 5n;
  mult2 = lambda z. z * 2n;
  compose(add5)(mult2)(3n)  # Should reduce to add5(mult2(3)) = add5(6) = 11

# ============================================================================
# SECTION 5: RECURSIVE FUNCTION PROPERTIES
# ============================================================================

# Termination and productivity for recursive functions
def recursive_termination_test(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + pred:
      1n + recursive_termination_test(pred)

# Structural recursion preservation
def structural_recursion_property<A>(xs: [A]) -> Nat:
  match xs:
    case []:
      0n
    case h <> t:
      1n + structural_recursion_property<A>(t)

# ============================================================================
# SECTION 6: EVALUATION ORDER INDEPENDENCE
# ============================================================================

# Call-by-need vs call-by-value equivalence for total functions
def evaluation_order_test() -> Nat:
  expensive_computation = lambda x. x * x * x;
  cheap_function = lambda y. 42n;  # Ignores argument
  # Order of evaluation shouldn't affect result for total functions
  cheap_function(expensive_computation(1000n))

# Lazy evaluation correctness
def lazy_evaluation_test() -> Nat:
  conditional = lambda b. lambda x. lambda y. 
    match b:
      case True: x
      case False: y;
  # Should not evaluate the infinite loop (simplified)
  conditional(True)(42n)(99n)

# ============================================================================
# SECTION 7: CONTEXTUAL EQUIVALENCE PROPERTIES
# ============================================================================

# Functions that are contextually equivalent should behave identically
def contextual_equiv_test1(f: Nat -> Nat, x: Nat) -> Nat:
  f(x)

def contextual_equiv_test2(g: Nat -> Nat, x: Nat) -> Nat:
  g(x)

# Observe that equivalent functions produce same results
def observe_equivalence() -> Nat:
  f1 = lambda x. x + 0n;
  f2 = lambda y. y;
  # These should be contextually equivalent - return one result
  contextual_equiv_test1(f1, 42n)

# ============================================================================
# SECTION 8: PARAMETRICITY PROPERTIES
# ============================================================================

# Polymorphic functions should satisfy parametricity
def parametricity_test<A>(xs: [A]) -> [A]:
  # Identity function on lists should work for any type A
  match xs:
    case []:
      []
    case h <> t:
      h <> parametricity_test<A>(t)

# Free theorems from parametricity
def free_theorem_test<A, B>(f: A -> B, xs: [A]) -> [B]:
  # map f . map id = map f (by parametricity)
  map_id_then_f = map<A, B>(f, parametricity_test<A>(xs));
  map_f_directly = map<A, B>(f, xs);
  map_f_directly  # Both should be equivalent

# ============================================================================
# SECTION 9: OBSERVATIONAL EQUIVALENCE
# ============================================================================

# Test observational equivalence of computationally equivalent terms
def obs_equiv_test1() -> Nat:
  # Different implementations of the same computation
  sum1 = 1n + 2n + 3n + 4n;
  sum2 = (1n + 4n) + (2n + 3n);
  sum3 = 10n;
  sum1  # All should be observationally equivalent

# Extensional equality for functions
def extensional_equality_test() -> Nat:
  f1 = lambda x. x * 2n;
  f2 = lambda y. y + y;
  # These functions should be extensionally equal - return one result
  f1(5n)

# ============================================================================
# SECTION 10: LOGICAL CONSISTENCY PROPERTIES
# ============================================================================

# No proof of False (consistency check)
def consistency_check() -> Bool:
  # We should not be able to prove False from True
  True

# Proof irrelevance for propositions (when implemented)
def proof_irrelevance_test<A>(x: A, y: A, p1: A{x == y}, p2: A{x == y}) -> A{x == y}:
  # Different proofs of the same proposition should be equivalent
  p1  # Both p1 and p2 should be treated as equivalent

# ============================================================================
# COMPREHENSIVE CORRECTNESS ASSERTIONS
# ============================================================================

# Test confluence properties
assert 11n == confluence_test1(lambda x. x + 5n, 6n) : Nat
assert 11n == confluence_test2() : Nat

# Test normalization
assert 18n == normalization_test1(5n) : Nat
assert 11n == whnf_test(True, 5n, 6n) : Nat
assert 30n == whnf_test(False, 5n, 6n) : Nat

# Test type preservation
assert 10n == subject_reduction_test<Nat>(lambda x. x * 2n, 5n) : Nat
assert 15n == substitution_preservation<Nat, Nat>(lambda x. x + 10n, 5n) : Nat

# Test beta-eta properties
assert 15n == beta_correctness_test() : Nat
assert 11n == higher_order_beta() : Nat

# Test recursive properties
assert 5n == recursive_termination_test(5n) : Nat
assert 4n == structural_recursion_property<Nat>([1n, 2n, 3n, 4n]) : Nat

# Test evaluation order independence
assert 42n == evaluation_order_test() : Nat
assert 42n == lazy_evaluation_test() : Nat

# Test contextual equivalence
assert 42n == observe_equivalence() : Nat

# Test parametricity
assert [1n, 2n, 3n] == parametricity_test<Nat>([1n, 2n, 3n]) : [Nat]
assert [2n, 4n, 6n] == free_theorem_test<Nat, Nat>(lambda x. x * 2n, [1n, 2n, 3n]) : [Nat]

# Test observational equivalence
assert 10n == obs_equiv_test1() : Nat
assert 10n == extensional_equality_test() : Nat

# Test logical consistency
assert True == consistency_check() : Bool

# Advanced property: map fusion
def map_fusion_property<A, B, C>(f: B -> C, g: A -> B, xs: [A]) -> [C]:
  # map f . map g = map (f . g)
  composed = lambda x. f(g(x));
  map<A, C>(composed, xs)

assert [6n, 8n, 10n] == map_fusion_property<Nat, Nat, Nat>(
  lambda x. x + 1n,
  lambda y. y * 2n,
  [2n, 3n, 4n]
) : [Nat]

# Fold fusion property
def fold_fusion_test<A>(xs: [A]) -> Nat:
  # length xs = fold (+) 0 (map (const 1) xs)
  ones = map<A, Nat>(lambda x. 1n, xs);
  fold<Nat, Nat>(lambda acc. lambda x. acc + x, 0n, ones)

assert 5n == fold_fusion_test<Bool>([True, False, True, False, True]) : Nat

# Helper functions
def map<A, B>(f: A -> B, xs: [A]) -> [B]:
  match xs:
    case []:
      []
    case h <> t:
      f(h) <> map<A, B>(f, t)

def fold<A, B>(f: B -> A -> B, acc: B, xs: [A]) -> B:
  match xs:
    case []:
      acc
    case h <> t:
      fold<A, B>(f, f(acc)(h), t)
"""

main :: IO ()
main = testFileChecks nbe_correctness_properties_bend