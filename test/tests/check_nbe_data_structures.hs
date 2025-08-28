{-# LANGUAGE MultilineStrings #-}

import Test

-- Test complex data structures and pattern matching for NbE
nbe_data_structures_bend :: String
nbe_data_structures_bend = """
# Binary tree datatype
type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>

# Tree operations
def tree_map<A,B>(f: A -> B, tree: Tree<A>) -> Tree<B>:
  match tree:
    case @Leaf{value}:
      @Leaf{f(value)}
    case @Node{left, right}:
      new_left = tree_map<A,B>(f, left)
      new_right = tree_map<A,B>(f, right)
      @Node{new_left, new_right}

def tree_sum(tree: Tree<Nat>) -> Nat:
  match tree:
    case @Leaf{value}:
      value
    case @Node{left, right}:
      left_sum = tree_sum(left)
      right_sum = tree_sum(right)
      left_sum + right_sum

# Maybe type for safe operations
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

def maybe_map<A,B>(f: A -> B, maybe: Maybe<A>) -> Maybe<B>:
  match maybe:
    case @None:
      @None
    case @Some{value}:
      @Some{f(value)}

def maybe_bind<A,B>(maybe: Maybe<A>, f: A -> Maybe<B>) -> Maybe<B>:
  match maybe:
    case @None:
      @None
    case @Some{value}:
      f(value)

# Safe division
def safe_divide(x: Nat, y: Nat) -> Maybe<Nat>:
  match y:
    case 0n:
      @None
    case 1n + pred:
      @Some{x / y}

# List zip operation
def zip<A,B>(xs: A[], ys: B[]) -> (A,B)[]:
  match xs:
    case []:
      []
    case x <> xs_rest:
      match ys:
        case []:
          []
        case y <> ys_rest:
          (x, y) <> zip<A,B>(xs_rest, ys_rest)

# Arithmetic functions for testing
def double_nat(x: Nat) -> Nat:
  x * 2n

def add_one(x: Nat) -> Nat:
  x + 1n

# Create test tree
def test_tree() -> Tree<Nat>:
  left_leaf = @Leaf{1n}
  right_subtree = @Node{@Leaf{3n}, @Leaf{5n}}
  @Node{left_leaf, right_subtree}

# Test tree operations
def expected_doubled_tree() -> Tree<Nat>:
  left_leaf = @Leaf{2n}
  right_subtree = @Node{@Leaf{6n}, @Leaf{10n}}
  @Node{left_leaf, right_subtree}

# Test tree sum
assert 9n == tree_sum(test_tree()) : Nat

# Test tree map
assert expected_doubled_tree() == tree_map<Nat,Nat>(double_nat, test_tree()) : Tree<Nat>

# Test maybe operations
assert @Some{6n} == maybe_map<Nat,Nat>(double_nat, @Some{3n}) : Maybe<Nat>
assert @None == maybe_map<Nat,Nat>(double_nat, @None) : Maybe<Nat>

# Test safe division
assert @Some{5n} == safe_divide(10n, 2n) : Maybe<Nat>
assert @None == safe_divide(10n, 0n) : Maybe<Nat>

# Test maybe bind
assert @Some{5n} == maybe_bind<Nat,Nat>(@Some{10n}, lambda x. safe_divide(x, 2n)) : Maybe<Nat>
assert @None == maybe_bind<Nat,Nat>(@Some{10n}, lambda x. safe_divide(x, 0n)) : Maybe<Nat>

# Test zip
assert [(1n, True), (2n, False)] == zip<Nat,Bool>([1n, 2n, 3n], [True, False]) : (Nat,Bool)[]
assert [] == zip<Nat,Bool>([], [True, False]) : (Nat,Bool)[]
"""

main :: IO ()
main = testFileChecks nbe_data_structures_bend