{-# LANGUAGE MultilineStrings #-}

import Test

-- Simplified Advanced Functional Programming Stress Tests for NbE
nbe_advanced_fp_simple_bend :: String
nbe_advanced_fp_simple_bend = """
# Simplified Advanced Functional Programming Stress Tests

# ============================================================================
# SECTION 1: ADVANCED COMBINATORS
# ============================================================================

# SKI Combinator Calculus
def S<A,B,C>(f: A -> B -> C, g: A -> B, x: A) -> C:
  f(x)(g(x))

def K<A,B>(x: A, y: B) -> A:
  x

def I<A>(x: A) -> A:
  x

# Church Numerals Implementation
def church_zero<A>(f: A -> A, x: A) -> A:
  x

def church_one<A>(f: A -> A, x: A) -> A:
  f(x)

def church_two<A>(f: A -> A, x: A) -> A:
  f(f(x))

def church_three<A>(f: A -> A, x: A) -> A:
  f(f(f(x)))

# ============================================================================
# SECTION 2: CONTINUATION PASSING STYLE (CPS)
# ============================================================================

# CPS factorial
def factorial_cps(n: Nat, k: Nat -> Nat) -> Nat:
  match n:
    case 0n:
      k(1n)
    case 1n + pred:
      factorial_cps(pred, lambda acc. k(n * acc))

# CPS list length
def length_cps<A>(xs: [A], k: Nat -> Nat) -> Nat:
  match xs:
    case []:
      k(0n)
    case h <> t:
      length_cps<A>(t, lambda acc. k(1n + acc))

# ============================================================================
# SECTION 3: ADVANCED RECURSIVE PATTERNS
# ============================================================================

# Mutual recursion with complex state
def even_odd_sum(n: Nat, acc_even: Nat, acc_odd: Nat) -> (Nat * Nat):
  match n:
    case 0n:
      return (acc_even, acc_odd)
    case 1n + pred:
      match pred:
        case 0n:
          return (acc_even, acc_odd + n)
        case 1n + pred2:
          result = even_odd_sum(pred2, acc_even + n, acc_odd)
          return result

# Ackermann function (small values only)
def ackermann(m: Nat, n: Nat) -> Nat:
  match m:
    case 0n:
      n + 1n
    case 1n + m_pred:
      match n:
        case 0n:
          ackermann(m_pred, 1n)
        case 1n + n_pred:
          ackermann(m_pred, ackermann(m, n_pred))

# ============================================================================
# SECTION 4: HIGHER-ORDER FUNCTION PATTERNS
# ============================================================================

# Function composition
def compose<A,B,C>(f: B -> C, g: A -> B, x: A) -> C:
  f(g(x))

# Apply function twice
def twice<A>(f: A -> A, x: A) -> A:
  f(f(x))

# Apply function three times
def thrice<A>(f: A -> A, x: A) -> A:
  f(f(f(x)))

# Curried functions
def add_curry(x: Nat) -> Nat -> Nat:
  lambda y. x + y

def mul_curry(x: Nat) -> Nat -> Nat:
  lambda y. x * y

# ============================================================================
# SECTION 5: MONADIC PATTERNS (SIMPLIFIED)
# ============================================================================

# State monad simulation
def state_bind<S,A,B>(m: S -> (A * S), f: A -> S -> (B * S), s: S) -> (B * S):
  pair = m(s)
  # Extract from pair - would need pattern matching support
  # For now, simplified
  f(fst<A,S>(pair))(snd<A,S>(pair))

# Helper functions for pairs
def fst<A,B>(pair: (A * B)) -> A:
  match pair:
    case (a, b):
      return a

def snd<A,B>(pair: (A * B)) -> B:
  match pair:
    case (a, b):
      return b

def state_return<S,A>(a: A, s: S) -> (A * S):
  (a, s)

# Reader monad simulation  
def reader_bind<R,A,B>(m: R -> A, f: A -> R -> B, r: R) -> B:
  f(m(r))(r)

def reader_return<R,A>(a: A, r: R) -> A:
  a

# ============================================================================
# SECTION 6: ADVANCED DATA STRUCTURE OPERATIONS
# ============================================================================

# Tree operations
type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>

def tree_map<A,B>(f: A -> B, tree: Tree<A>) -> Tree<B>:
  match tree:
    case @Leaf{value}:
      @Leaf{f(value)}
    case @Node{left, right}:
      @Node{tree_map<A,B>(f, left), tree_map<A,B>(f, right)}

def tree_fold<A,B>(leaf_f: A -> B, node_f: B -> B -> B, tree: Tree<A>) -> B:
  match tree:
    case @Leaf{value}:
      leaf_f(value)
    case @Node{left, right}:
      node_f(tree_fold<A,B>(leaf_f, node_f, left))(tree_fold<A,B>(leaf_f, node_f, right))

# ============================================================================
# COMPREHENSIVE ASSERTIONS
# ============================================================================

# Test SKI Combinator Laws
assert 42n == I<Nat>(42n) : Nat
assert 17n == K<Nat, Bool>(17n, True) : Nat  
assert 8n == S<Nat, Nat, Nat>(lambda x. lambda y. x + y, lambda x. x * 2n, 2n) : Nat

# Test Church Numerals
assert 1n == church_zero<Nat>(lambda x. x + 1n, 1n) : Nat
assert 2n == church_one<Nat>(lambda x. x + 1n, 1n) : Nat
assert 3n == church_two<Nat>(lambda x. x + 1n, 1n) : Nat
assert 4n == church_three<Nat>(lambda x. x + 1n, 1n) : Nat

# Test CPS Functions
assert 120n == factorial_cps(5n, lambda x. x) : Nat
assert 4n == length_cps<Nat>([1n, 2n, 3n, 4n], lambda x. x) : Nat

# Test Complex Recursive Functions  
assert (12n, 9n) == even_odd_sum(6n, 0n, 0n) : (Nat * Nat)  # evens: 2+4+6=12, odds: 1+3+5=9

# Test Ackermann (small values)
assert 3n == ackermann(1n, 1n) : Nat
assert 7n == ackermann(2n, 2n) : Nat

# Test Higher-Order Functions
assert 11n == compose<Nat, Nat, Nat>(lambda x. x + 1n, lambda x. x * 2n, 5n) : Nat
assert 20n == twice<Nat>(lambda x. x * 2n, 5n) : Nat
assert 40n == thrice<Nat>(lambda x. x * 2n, 5n) : Nat

# Test Curried Functions
assert 8n == add_curry(3n)(5n) : Nat
assert 15n == mul_curry(3n)(5n) : Nat

# Test Monadic Patterns
assert (33n, 25n) == state_bind<Nat, Nat, Nat>(
  lambda s. (s + 1n, s * 2n),
  lambda a. lambda s. (a * 3n, s + 5n),
  10n
) : (Nat * Nat)

# Test Reader Monad
assert 15n == reader_bind<Nat, Nat, Nat>(
  lambda r. r * 2n,
  lambda a. lambda r. a + r,
  5n
) : Nat  # (5 * 2) + 5 = 15

# Test Tree Operations
assert @Node{@Leaf{4n}, @Leaf{6n}} == tree_map<Nat, Nat>(lambda x. x * 2n, @Node{@Leaf{2n}, @Leaf{3n}}) : Tree<Nat>

assert 5n == tree_fold<Nat, Nat>(lambda x. x, lambda l. lambda r. l + r, @Node{@Leaf{2n}, @Leaf{3n}}) : Nat

# Test function composition chains  
assert 9n == compose<Nat, Nat, Nat>(lambda x. x + 1n, lambda x. x * 2n, 4n) : Nat  # (4 * 2) + 1 = 9

# Test nested applications
assert 4n == (lambda f. f(f(f(f(0n)))))(lambda x. x + 1n) : Nat
"""

main :: IO ()
main = testFileChecks nbe_advanced_fp_simple_bend