{-# LANGUAGE MultilineStrings #-}

import Test

-- Canonical Forms Equality Tests
-- Verifies combinators and data structures work by comparing canonical forms
nbe_canonical_forms_bend :: String
nbe_canonical_forms_bend = """
# Canonical Forms Equality Verification Tests

# ============================================================================
# SECTION 1: SKI COMBINATOR CANONICAL FORMS
# ============================================================================

# SKI Combinators
def S<A,B,C>(f: A -> B -> C, g: A -> B, x: A) -> C:
  f(x)(g(x))

def K<A,B>(x: A, y: B) -> A:
  x

def I<A>(x: A) -> A:
  x

# Test canonical forms of combinator applications
def test_K_canonical() -> Nat:
  K<Nat, Bool>(5n, True)  # Should canonically reduce to 5n

def test_I_canonical() -> Nat:
  I<Nat>(42n)  # Should canonically reduce to 42n

def test_S_canonical() -> Nat:
  # S(K)(K)(x) should reduce to K(x)(K(x)) = x
  f = K<Nat, Nat>;
  g = K<Nat, Nat>;
  x = 7n;
  S<Nat, Nat, Nat>(f, g, x)

# Test SKI identity: S K K = I
def test_SKK_identity(x: Nat) -> Nat:
  # S K K x should equal I x
  left_side = S<Nat, Nat, Nat>(K<Nat, Nat -> Nat>, K<Nat, Nat>, x);
  right_side = I<Nat>(x);
  left_side  # Both should be canonical x

# ============================================================================
# SECTION 2: CHURCH NUMERAL CANONICAL FORMS
# ============================================================================

# Church Numerals
def church_zero<A>(f: A -> A, x: A) -> A:
  x

def church_one<A>(f: A -> A, x: A) -> A:
  f(x)

def church_two<A>(f: A -> A, x: A) -> A:
  f(f(x))

def church_three<A>(f: A -> A, x: A) -> A:
  f(f(f(x)))

# Church successor
def church_succ<A>(n: (A -> A) -> A -> A, f: A -> A, x: A) -> A:
  f(n(f, x))

# Convert Church numeral to Nat for canonical comparison
def church_to_nat(n: (Nat -> Nat) -> Nat -> Nat) -> Nat:
  inc = lambda x. x + 1n;
  n(inc, 0n)

# Test Church numeral canonical forms
def test_church_zero_canonical() -> Nat:
  church_to_nat(church_zero<Nat>)  # Should be 0n

def test_church_one_canonical() -> Nat:
  church_to_nat(church_one<Nat>)  # Should be 1n

def test_church_succ_canonical() -> Nat:
  # church_succ(church_two) should equal church_three
  succ_two = church_succ<Nat>(church_two<Nat>);
  church_to_nat(succ_two)  # Should be 3n

# ============================================================================
# SECTION 3: FUNCTION COMPOSITION CANONICAL FORMS
# ============================================================================

def compose<A,B,C>(f: B -> C, g: A -> B, x: A) -> C:
  f(g(x))

def add_one(x: Nat) -> Nat:
  x + 1n

def mul_two(x: Nat) -> Nat:
  x * 2n

# Test composition canonical forms
def test_compose_canonical() -> Nat:
  # (add_one . mul_two)(5) should canonically equal add_one(mul_two(5)) = add_one(10) = 11
  compose<Nat, Nat, Nat>(add_one, mul_two, 5n)

def test_compose_associativity() -> Nat:
  # (f . g) . h should equal f . (g . h) canonically
  add_two = lambda x. x + 2n;
  # Left: (add_one . mul_two) . add_two
  left_comp = compose<Nat, Nat, Nat>(add_one, mul_two);
  left_result = compose<Nat, Nat, Nat>(left_comp, add_two, 3n);
  left_result  # Should be add_one(mul_two(add_two(3))) = add_one(mul_two(5)) = add_one(10) = 11

# ============================================================================
# SECTION 4: LIST OPERATION CANONICAL FORMS
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

# Test list operation canonical forms
def test_map_canonical() -> [Nat]:
  # map(+1) [1,2,3] should canonically equal [2,3,4]
  map<Nat, Nat>(add_one, [1n, 2n, 3n])

def test_fold_canonical() -> Nat:
  # fold(+) 0 [1,2,3,4] should canonically equal 10
  add_func = lambda acc. lambda x. acc + x;
  fold<Nat, Nat>(add_func, 0n, [1n, 2n, 3n, 4n])

# Test map-fold fusion canonical form
def test_map_fold_fusion() -> Nat:
  # fold(+) 0 (map(*2) [1,2,3]) should canonically equal fold(+) 0 [2,4,6] = 12
  doubled_list = map<Nat, Nat>(mul_two, [1n, 2n, 3n]);
  add_func = lambda acc. lambda x. acc + x;
  fold<Nat, Nat>(add_func, 0n, doubled_list)

# ============================================================================
# SECTION 5: MAYBE MONAD CANONICAL FORMS
# ============================================================================

type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

def maybe_map<A, B>(f: A -> B, ma: Maybe<A>) -> Maybe<B>:
  match ma:
    case @None:
      @None
    case @Some{value}:
      @Some{f(value)}

def maybe_bind<A, B>(ma: Maybe<A>, f: A -> Maybe<B>) -> Maybe<B>:
  match ma:
    case @None:
      @None
    case @Some{value}:
      f(value)

def maybe_pure<A>(x: A) -> Maybe<A>:
  @Some{x}

# Test Maybe monad canonical forms
def test_maybe_map_canonical() -> Maybe<Nat>:
  # maybe_map(+1) (Some 5) should canonically equal Some 6
  maybe_map<Nat, Nat>(add_one, @Some{5n})

def test_maybe_bind_canonical() -> Maybe<Nat>:
  # bind (Some 5) (\\x -> Some (x + 1)) should canonically equal Some 6
  f = lambda x. @Some{x + 1n};
  maybe_bind<Nat, Nat>(@Some{5n}, f)

# Test monad laws canonical forms
def test_left_identity_canonical() -> Maybe<Nat>:
  # bind (pure x) f should canonically equal f x
  x = 7n;
  f = lambda y. @Some{y * 2n};
  maybe_bind<Nat, Nat>(maybe_pure<Nat>(x), f)  # Should be Some 14

def test_right_identity_canonical() -> Maybe<Nat>:
  # bind m pure should canonically equal m
  m = @Some{9n};
  maybe_bind<Nat, Nat>(m, maybe_pure<Nat>)  # Should be Some 9

# ============================================================================
# SECTION 6: TREE STRUCTURE CANONICAL FORMS
# ============================================================================

type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>

def tree_map<A, B>(f: A -> B, tree: Tree<A>) -> Tree<B>:
  match tree:
    case @Leaf{value}:
      @Leaf{f(value)}
    case @Node{left, right}:
      @Node{tree_map<A, B>(f, left), tree_map<A, B>(f, right)}

def tree_fold<A, B>(leaf_f: A -> B, node_f: B -> B -> B, tree: Tree<A>) -> B:
  match tree:
    case @Leaf{value}:
      leaf_f(value)
    case @Node{left, right}:
      node_f(tree_fold<A, B>(leaf_f, node_f, left))(tree_fold<A, B>(leaf_f, node_f, right))

# Test tree operation canonical forms
def test_tree_map_canonical() -> Tree<Nat>:
  # tree_map(+1) (Node (Leaf 1) (Leaf 2)) should canonically equal Node (Leaf 2) (Leaf 3)
  tree = @Node{@Leaf{1n}, @Leaf{2n}};
  tree_map<Nat, Nat>(add_one, tree)

def test_tree_fold_canonical() -> Nat:
  # tree_fold(id)(+) (Node (Leaf 3) (Leaf 7)) should canonically equal 10
  tree = @Node{@Leaf{3n}, @Leaf{7n}};
  id_func = lambda x. x;
  add_func = lambda x. lambda y. x + y;
  tree_fold<Nat, Nat>(id_func, add_func, tree)

# ============================================================================
# SECTION 7: CPS CANONICAL FORM VERIFICATION
# ============================================================================

# CPS transformations should preserve semantics
def factorial_direct(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n + pred:
      n * factorial_direct(pred)

def factorial_cps(n: Nat, k: Nat -> Nat) -> Nat:
  match n:
    case 0n:
      k(1n)
    case 1n + pred:
      factorial_cps(pred, lambda acc. k(n * acc))

# Test CPS canonical equivalence
def test_factorial_cps_canonical() -> Nat:
  # factorial_cps(4, id) should canonically equal factorial_direct(4) = 24
  id_cont = lambda x. x;
  factorial_cps(4n, id_cont)

def list_sum_direct(xs: [Nat]) -> Nat:
  match xs:
    case []:
      0n
    case h <> t:
      h + list_sum_direct(t)

def list_sum_cps(xs: [Nat], k: Nat -> Nat) -> Nat:
  match xs:
    case []:
      k(0n)
    case h <> t:
      list_sum_cps(t, lambda acc. k(h + acc))

def test_list_sum_cps_canonical() -> Nat:
  # list_sum_cps([1,2,3,4], id) should canonically equal list_sum_direct([1,2,3,4]) = 10
  id_cont = lambda x. x;
  list_sum_cps([1n, 2n, 3n, 4n], id_cont)

# ============================================================================
# COMPREHENSIVE CANONICAL FORM ASSERTIONS
# ============================================================================

# SKI Combinator canonical form tests
assert 5n == test_K_canonical() : Nat
assert 42n == test_I_canonical() : Nat
assert 7n == test_S_canonical() : Nat
assert 10n == test_SKK_identity(10n) : Nat

# Church numeral canonical form tests  
assert 0n == test_church_zero_canonical() : Nat
assert 1n == test_church_one_canonical() : Nat
assert 3n == test_church_succ_canonical() : Nat

# Function composition canonical form tests
assert 11n == test_compose_canonical() : Nat
assert 11n == test_compose_associativity() : Nat

# List operation canonical form tests
assert [2n, 3n, 4n] == test_map_canonical() : [Nat]
assert 10n == test_fold_canonical() : Nat
assert 12n == test_map_fold_fusion() : Nat

# Maybe monad canonical form tests
assert @Some{6n} == test_maybe_map_canonical() : Maybe<Nat>
assert @Some{6n} == test_maybe_bind_canonical() : Maybe<Nat>
assert @Some{14n} == test_left_identity_canonical() : Maybe<Nat>
assert @Some{9n} == test_right_identity_canonical() : Maybe<Nat>

# Tree structure canonical form tests
assert @Node{@Leaf{2n}, @Leaf{3n}} == test_tree_map_canonical() : Tree<Nat>
assert 10n == test_tree_fold_canonical() : Nat

# CPS canonical equivalence tests
assert 24n == test_factorial_cps_canonical() : Nat
assert 24n == factorial_direct(4n) : Nat  # Direct comparison
assert 10n == test_list_sum_cps_canonical() : Nat
assert 10n == list_sum_direct([1n, 2n, 3n, 4n]) : Nat  # Direct comparison

# Advanced canonical equivalence assertions
# Test that SKK is extensionally equal to I
assert 15n == test_SKK_identity(15n) : Nat
assert 15n == I<Nat>(15n) : Nat

# Test Church numeral arithmetic canonical forms
def church_add<A>(m: (A -> A) -> A -> A, n: (A -> A) -> A -> A, f: A -> A, x: A) -> A:
  m(f, n(f, x))

def test_church_add_canonical() -> Nat:
  # church_add(church_two, church_three) should canonically equal church_five = 5
  church_five = church_add<Nat>(church_two<Nat>, church_three<Nat>);
  church_to_nat(church_five)

assert 5n == test_church_add_canonical() : Nat

# Test functor laws canonical forms (map id = id)
def test_map_id_law() -> [Nat]:
  # map(id) should be canonically equivalent to id
  id_func = lambda x. x;
  map<Nat, Nat>(id_func, [1n, 2n, 3n])

assert [1n, 2n, 3n] == test_map_id_law() : [Nat]

# Test composition canonical equivalence
def test_map_compose_law() -> [Nat]:
  # map(f . g) should canonically equal map(f) . map(g)
  composed = lambda x. add_one(mul_two(x));
  map<Nat, Nat>(composed, [1n, 2n])

def test_map_compose_separate() -> [Nat]:
  # Separate application: map(add_one, map(mul_two, [1,2]))
  doubled = map<Nat, Nat>(mul_two, [1n, 2n]);
  map<Nat, Nat>(add_one, doubled)

assert [3n, 5n] == test_map_compose_law() : [Nat]
assert [3n, 5n] == test_map_compose_separate() : [Nat]
"""

main :: IO ()
main = testFileChecks nbe_canonical_forms_bend