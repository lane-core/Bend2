{-# LANGUAGE MultilineStrings #-}

import Test

-- Mathematical Property Correspondence Tests
-- Computes values in Bend and verifies correspondence in Haskell assertions
nbe_correspondence_properties_bend :: String
nbe_correspondence_properties_bend = """
# Mathematical Property Correspondence Tests
# Values computed in Bend, correspondence verified in Haskell assertions

# ============================================================================
# SECTION 1: ALGEBRAIC STRUCTURE CORRESPONDENCE
# ============================================================================

# Addition associativity: (a + b) + c vs a + (b + c)
def add_assoc_left(a: Nat, b: Nat, c: Nat) -> Nat:
  (a + b) + c

def add_assoc_right(a: Nat, b: Nat, c: Nat) -> Nat:
  a + (b + c)

# Addition commutativity: a + b vs b + a
def add_comm_left(a: Nat, b: Nat) -> Nat:
  a + b

def add_comm_right(a: Nat, b: Nat) -> Nat:
  b + a

# Multiplication distributivity: a * (b + c) vs (a * b) + (a * c)
def mul_dist_left(a: Nat, b: Nat, c: Nat) -> Nat:
  a * (b + c)

def mul_dist_right(a: Nat, b: Nat, c: Nat) -> Nat:
  (a * b) + (a * c)

# ============================================================================
# SECTION 2: FUNCTIONAL CORRESPONDENCE
# ============================================================================

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

def compose<A, B, C>(f: B -> C, g: A -> B, x: A) -> C:
  f(g(x))

def id<A>(x: A) -> A:
  x

# Functor identity: map(id, xs) vs xs
def map_id_test() -> [Nat]:
  id_func = lambda x. x;
  map<Nat, Nat>(id_func, [1n, 2n, 3n])

# Functor composition: map(f . g, xs) vs map(f, map(g, xs))
def map_compose_fused() -> [Nat]:
  f = lambda x. x + 1n;
  g = lambda x. x * 2n;
  composed = lambda x. f(g(x));
  map<Nat, Nat>(composed, [1n, 2n, 3n])

def map_compose_separate() -> [Nat]:
  f = lambda x. x + 1n;
  g = lambda x. x * 2n;
  mapped_g = map<Nat, Nat>(g, [1n, 2n, 3n]);
  map<Nat, Nat>(f, mapped_g)

# ============================================================================
# SECTION 3: CATEGORICAL CORRESPONDENCE
# ============================================================================

# Left identity: id . f vs f
def left_identity_compose() -> Nat:
  f = lambda x. x + 10n;
  compose<Nat, Nat, Nat>(f, id<Nat>, 5n)

def left_identity_direct() -> Nat:
  f = lambda x. x + 10n;
  f(5n)

# Right identity: f . id vs f  
def right_identity_compose() -> Nat:
  f = lambda x. x * 3n;
  compose<Nat, Nat, Nat>(id<Nat>, f, 7n)

def right_identity_direct() -> Nat:
  f = lambda x. x * 3n;
  f(7n)

# ============================================================================
# SECTION 4: RECURSIVE CORRESPONDENCE
# ============================================================================

# Factorial - direct vs tail-recursive implementation
def factorial_direct(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n + pred:
      n * factorial_direct(pred)

def factorial_tail_helper(n: Nat, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n + pred:
      factorial_tail_helper(pred, n * acc)

def factorial_tail(n: Nat) -> Nat:
  factorial_tail_helper(n, 1n)

# Sum - recursive vs fold implementation
def sum_recursive(xs: [Nat]) -> Nat:
  match xs:
    case []:
      0n
    case h <> t:
      h + sum_recursive(t)

def sum_fold(xs: [Nat]) -> Nat:
  add_func = lambda acc. lambda x. acc + x;
  fold<Nat, Nat>(add_func, 0n, xs)

# ============================================================================
# SECTION 5: HOMOMORPHISM CORRESPONDENCE
# ============================================================================

def length<A>(xs: [A]) -> Nat:
  match xs:
    case []:
      0n
    case h <> t:
      1n + length<A>(t)

def append<A>(xs: [A], ys: [A]) -> [A]:
  match xs:
    case []:
      ys
    case h <> t:
      h <> append<A>(t, ys)

# Length homomorphism: length(xs ++ ys) vs length(xs) + length(ys)
def length_concat() -> Nat:
  xs = [1n, 2n, 3n];
  ys = [4n, 5n];
  length<Nat>(append<Nat>(xs, ys))

def length_sum() -> Nat:
  xs = [1n, 2n, 3n];
  ys = [4n, 5n];
  length<Nat>(xs) + length<Nat>(ys)

# Map homomorphism: map(f, xs ++ ys) vs map(f, xs) ++ map(f, ys)
def map_homomorphism_concat() -> [Nat]:
  f = lambda x. x * 2n;
  xs = [1n, 2n];
  ys = [3n, 4n];
  map<Nat, Nat>(f, append<Nat>(xs, ys))

def map_homomorphism_separate() -> [Nat]:
  f = lambda x. x * 2n;
  xs = [1n, 2n];
  ys = [3n, 4n];
  mapped_xs = map<Nat, Nat>(f, xs);
  mapped_ys = map<Nat, Nat>(f, ys);
  append<Nat>(mapped_xs, mapped_ys)

# ============================================================================
# SECTION 6: MONADIC CORRESPONDENCE
# ============================================================================

type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

def maybe_bind<A, B>(ma: Maybe<A>, f: A -> Maybe<B>) -> Maybe<B>:
  match ma:
    case @None:
      @None
    case @Some{value}:
      f(value)

def maybe_pure<A>(x: A) -> Maybe<A>:
  @Some{x}

# Left identity: bind(pure(x), f) vs f(x)
def monad_left_identity_bind() -> Maybe<Nat>:
  x = 42n;
  f = lambda y. @Some{y * 2n};
  maybe_bind<Nat, Nat>(maybe_pure<Nat>(x), f)

def monad_left_identity_direct() -> Maybe<Nat>:
  x = 42n;
  f = lambda y. @Some{y * 2n};
  f(x)

# Right identity: bind(m, pure) vs m
def monad_right_identity_bind() -> Maybe<Nat>:
  m = @Some{17n};
  maybe_bind<Nat, Nat>(m, maybe_pure<Nat>)

def monad_right_identity_direct() -> Maybe<Nat>:
  @Some{17n}

# ============================================================================
# SECTION 7: CHURCH ENCODING CORRESPONDENCE
# ============================================================================

def church_zero<A>(f: A -> A, x: A) -> A:
  x

def church_one<A>(f: A -> A, x: A) -> A:
  f(x)

def church_two<A>(f: A -> A, x: A) -> A:
  f(f(x))

def church_three<A>(f: A -> A, x: A) -> A:
  f(f(f(x)))

def church_succ<A>(n: (A -> A) -> A -> A, f: A -> A, x: A) -> A:
  f(n(f, x))

def church_add<A>(m: (A -> A) -> A -> A, n: (A -> A) -> A -> A, f: A -> A, x: A) -> A:
  m(f, n(f, x))

def church_to_nat(n: (Nat -> Nat) -> Nat -> Nat) -> Nat:
  inc = lambda x. x + 1n;
  n(inc, 0n)

# Test Church numeral arithmetic
def church_two_plus_three() -> Nat:
  result = church_add<Nat>(church_two<Nat>, church_three<Nat>);
  church_to_nat(result)

def church_succ_two() -> Nat:
  result = church_succ<Nat>(church_two<Nat>);
  church_to_nat(result)

# ============================================================================
# CANONICAL FORM VERIFICATION ASSERTIONS
# ============================================================================

# Test algebraic correspondence
assert 15n == add_assoc_left(3n, 5n, 7n) : Nat
assert 15n == add_assoc_right(3n, 5n, 7n) : Nat
assert 13n == add_comm_left(4n, 9n) : Nat
assert 13n == add_comm_right(4n, 9n) : Nat
assert 27n == mul_dist_left(3n, 4n, 5n) : Nat
assert 27n == mul_dist_right(3n, 4n, 5n) : Nat

# Test functor correspondence  
assert [1n, 2n, 3n] == map_id_test() : [Nat]
assert [3n, 5n, 7n] == map_compose_fused() : [Nat]
assert [3n, 5n, 7n] == map_compose_separate() : [Nat]

# Test categorical correspondence
assert 15n == left_identity_compose() : Nat
assert 15n == left_identity_direct() : Nat
assert 21n == right_identity_compose() : Nat
assert 21n == right_identity_direct() : Nat

# Test recursive correspondence
assert 120n == factorial_direct(5n) : Nat
assert 120n == factorial_tail(5n) : Nat
assert 10n == sum_recursive([1n, 2n, 3n, 4n]) : Nat
assert 10n == sum_fold([1n, 2n, 3n, 4n]) : Nat

# Test homomorphism correspondence
assert 5n == length_concat() : Nat
assert 5n == length_sum() : Nat
assert [2n, 4n, 6n, 8n] == map_homomorphism_concat() : [Nat]
assert [2n, 4n, 6n, 8n] == map_homomorphism_separate() : [Nat]

# Test monadic correspondence  
assert @Some{84n} == monad_left_identity_bind() : Maybe<Nat>
assert @Some{84n} == monad_left_identity_direct() : Maybe<Nat>
assert @Some{17n} == monad_right_identity_bind() : Maybe<Nat>
assert @Some{17n} == monad_right_identity_direct() : Maybe<Nat>

# Test Church encoding correspondence
assert 0n == church_to_nat(church_zero<Nat>) : Nat
assert 1n == church_to_nat(church_one<Nat>) : Nat
assert 2n == church_to_nat(church_two<Nat>) : Nat
assert 3n == church_to_nat(church_three<Nat>) : Nat
assert 5n == church_two_plus_three() : Nat
assert 3n == church_succ_two() : Nat

# Advanced correspondence: verify map fusion preserves results
def map_twice(f: Nat -> Nat, g: Nat -> Nat, xs: [Nat]) -> [Nat]:
  map<Nat, Nat>(f, map<Nat, Nat>(g, xs))

def map_fused(f: Nat -> Nat, g: Nat -> Nat, xs: [Nat]) -> [Nat]:
  composed = lambda x. f(g(x));
  map<Nat, Nat>(composed, xs)

def test_map_fusion() -> [Nat]:
  f = lambda x. x + 1n;
  g = lambda x. x * 2n;
  test_data = [1n, 2n, 3n];
  map_twice(f, g, test_data)

def test_map_fusion_direct() -> [Nat]:
  f = lambda x. x + 1n;
  g = lambda x. x * 2n;
  test_data = [1n, 2n, 3n];
  map_fused(f, g, test_data)

assert [3n, 5n, 7n] == test_map_fusion() : [Nat]
assert [3n, 5n, 7n] == test_map_fusion_direct() : [Nat]

# Verify fold left-right equivalence for associative operations
def fold_left<A, B>(f: A -> B -> A, acc: A, xs: [B]) -> A:
  match xs:
    case []:
      acc
    case h <> t:
      fold_left<A, B>(f, f(acc)(h), t)

def fold_right<A, B>(f: A -> B -> B, xs: [A], acc: B) -> B:
  match xs:
    case []:
      acc
    case h <> t:
      f(h)(fold_right<A, B>(f, t, acc))

def test_fold_left_assoc() -> Nat:
  add_left = lambda acc. lambda x. acc + x;
  test_list = [1n, 2n, 3n, 4n];
  fold_left<Nat, Nat>(add_left, 0n, test_list)

def test_fold_right_assoc() -> Nat:
  add_right = lambda x. lambda acc. x + acc;
  test_list = [1n, 2n, 3n, 4n];
  fold_right<Nat, Nat>(add_right, test_list, 0n)

assert 10n == test_fold_left_assoc() : Nat
assert 10n == test_fold_right_assoc() : Nat
"""

main :: IO ()
main = testFileChecks nbe_correspondence_properties_bend