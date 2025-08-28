{-# LANGUAGE MultilineStrings #-}

import Test

-- Advanced Functional Programming Stress Tests for NbE
-- Tests complex patterns, higher-kinded types, and advanced combinators
nbe_advanced_fp_bend :: String
nbe_advanced_fp_bend = """
# Advanced Functional Programming Stress Tests

# ============================================================================
# SECTION 1: ADVANCED COMBINATORS AND FUNCTION COMPOSITION
# ============================================================================

# Y Combinator (Fixed Point Combinator)
def Y<A>(f: (A -> A) -> (A -> A)) -> A -> A:
  lambda x. f(Y<A>(f))(x)

# SKI Combinator Calculus
def S<A,B,C>(f: A -> B -> C, g: A -> B, x: A) -> C:
  f(x)(g(x))

def K<A,B>(x: A, y: B) -> A:
  x

def I<A>(x: A) -> A:
  x

# Church Numerals Implementation
def Church<A>(n: Nat, f: A -> A, x: A) -> A:
  match n:
    case 0n:
      x
    case 1n + pred:
      f(Church<A>(pred, f, x))

# ============================================================================
# SECTION 2: ADVANCED DATA STRUCTURES AND TRANSFORMATIONS
# ============================================================================

# Rose Tree (Multi-way tree)
type Rose<A: Set>:
  case @Node:
    value: A
    children: [Rose<A>]

def rose_map<A,B>(f: A -> B, tree: Rose<A>) -> Rose<B>:
  match tree:
    case @Node{value, children}:
      @Node{f(value), map_rose_trees<A,B>(f, children)}

# Helper for rose_map
def map_rose_trees<A,B>(f: A -> B, trees: [Rose<A>]) -> [Rose<B>]:
  match trees:
    case []:
      []
    case h :: t:
      rose_map<A,B>(f, h) :: map_rose_trees<A,B>(f, t)

def rose_fold<A,B>(f: A -> [B] -> B, tree: Rose<A>) -> B:
  match tree:
    case @Node{value, children}:
      let results = map_rose_fold<A,B>(f, children)
      f(value)(results)

# Helper for rose_fold
def map_rose_fold<A,B>(f: A -> [B] -> B, trees: [Rose<A>]) -> [B]:
  match trees:
    case []:
      []
    case h :: t:
      rose_fold<A,B>(f, h) :: map_rose_fold<A,B>(f, t)

# Finger Tree (Advanced functional data structure)  
type FingerTree<A: Set>:
  case @Empty:
  case @Single:
    item: A
  case @Deep:
    left: [A]
    middle: FingerTree<[A]>
    right: [A]

# ============================================================================
# SECTION 3: CONTINUATION PASSING STYLE (CPS)
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
    case h :: t:
      length_cps<A>(t, lambda acc. k(1n + acc))

# ============================================================================
# SECTION 4: ADVANCED PATTERN MATCHING AND DEPENDENT PATTERNS
# ============================================================================

# Vector with length in type (simplified)
type Vec<A: Set>:
  case @VNil:
  case @VCons:
    head: A
    tail: Vec<A>

def vec_length<A>(v: Vec<A>) -> Nat:
  match v:
    case @VNil:
      0n
    case @VCons{head, tail}:
      1n + vec_length<A>(tail)

def vec_zip<A,B>(v1: Vec<A>, v2: Vec<B>) -> Vec<(A * B)>:
  match v1:
    case @VNil:
      @VNil
    case @VCons{head1, tail1}:
      match v2:
        case @VNil:
          @VNil
        case @VCons{head2, tail2}:
          @VCons{(head1, head2), vec_zip<A,B>(tail1, tail2)}

# ============================================================================
# SECTION 5: ADVANCED MONADIC PATTERNS
# ============================================================================

# State monad simulation
def state_bind<S,A,B>(m: S -> (A * S), f: A -> S -> (B * S), s: S) -> (B * S):
  let (a, s') = m(s)
  f(a)(s')

def state_return<S,A>(a: A, s: S) -> (A * S):
  (a, s)

# Reader monad simulation  
def reader_bind<R,A,B>(m: R -> A, f: A -> R -> B, r: R) -> B:
  f(m(r))(r)

def reader_return<R,A>(a: A, r: R) -> A:
  a

# ============================================================================
# SECTION 6: COMPLEX RECURSIVE PATTERNS
# ============================================================================

# Mutual recursion with complex state
def even_odd_sum(n: Nat, acc_even: Nat, acc_odd: Nat) -> (Nat * Nat):
  match n:
    case 0n:
      (acc_even, acc_odd)
    case 1n + pred:
      match pred:
        case 0n:
          (acc_even, acc_odd + n)
        case 1n + pred2:
          let (e, o) = even_odd_sum(pred2, acc_even + n, acc_odd)
          (e, o)

# Ackermann function (computationally intensive)
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
# COMPREHENSIVE ASSERTION TESTS
# ============================================================================

# Test SKI Combinator Laws
assert 42n == I<Nat>(42n) : Nat
assert 17n == K<Nat, Bool>(17n, True) : Nat  
assert 8n == S<Nat, Nat, Nat>(lambda x. lambda y. x + y, lambda x. x * 2n, 2n) : Nat

# Test Church Numerals
assert 16n == Church<Nat>(4n, lambda x. x * 2n, 1n) : Nat
assert 1000n == Church<Nat>(3n, lambda x. x * 10n, 1n) : Nat

# Test Advanced Data Structure Operations
let test_rose = @Node{5n, [@Node{2n, []}, @Node{3n, [@Node{1n, []}]}]}
let doubled_rose = rose_map<Nat, Nat>(lambda x. x * 2n, test_rose)
assert @Node{10n, [@Node{4n, []}, @Node{6n, [@Node{2n, []}]}]} == doubled_rose : Rose<Nat>

let sum_rose = rose_fold<Nat, Nat>(lambda val. lambda children. val + list_sum(children), test_rose)
assert 11n == sum_rose : Nat

# Test CPS Functions
assert 120n == factorial_cps(5n, lambda x. x) : Nat
assert 4n == length_cps<Nat>([1n, 2n, 3n, 4n], lambda x. x) : Nat

# Test Vector Operations
let vec1 = @VCons{1n, @VCons{2n, @VNil}}
let vec2 = @VCons{10n, @VCons{20n, @VNil}}
let zipped = vec_zip<Nat, Nat>(vec1, vec2)
assert @VCons{(1n, 10n), @VCons{(2n, 20n), @VNil}} == zipped : Vec<(Nat * Nat)>

assert 2n == vec_length<Nat>(vec1) : Nat

# Test Complex Recursive Functions
let (evens, odds) = even_odd_sum(6n, 0n, 0n)
assert 12n == evens : Nat  # 2 + 4 + 6 = 12
assert 9n == odds : Nat    # 1 + 3 + 5 = 9

# Test Ackermann (small values to avoid explosion)
assert 3n == ackermann(1n, 1n) : Nat
assert 7n == ackermann(2n, 2n) : Nat

# Test Monadic Patterns
let state_result = state_bind<Nat, Nat, Nat>(
  lambda s. (s + 1n, s * 2n),
  lambda a. lambda s. (a * 3n, s + 5n),
  10n
)
assert (33n, 25n) == state_result : (Nat * Nat)

# Test Reader Monad
let reader_result = reader_bind<Nat, Nat, Nat>(
  lambda r. r * 2n,
  lambda a. lambda r. a + r,
  5n
)
assert 15n == reader_result : Nat  # (5 * 2) + 5 = 15

# Helper function for list sum used in tests
def list_sum(xs: [Nat]) -> Nat:
  match xs:
    case []:
      0n
    case h :: t:
      h + list_sum(t)
"""

main :: IO ()
main = testFileChecks nbe_advanced_fp_bend