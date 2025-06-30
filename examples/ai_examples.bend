# Bend has Python-like syntax, Haskell-like evaluation, and Lean-like types

# Native Types
# ------------

# - Empty         ::=                  -- empty
# - Unit          ::= ()               -- unit
# - Bool          ::= True, False      -- boolean
# - Nat           ::= 0n, 1n+pred      -- natural number
# - List(T)       ::= [], head <> tail -- polymorphic list
# - @{@A,@B,...}  ::= @A, @B, ...      -- inline enum
# - any x:A. B(x) ::= (x, y)           -- dependent pair
# - all x:A. B(x) ::= λx. f(x)         -- dependent function
# - T{a == b}     ::= finally          -- propositional equality

# Example Functions
# -----------------

# Identity
def id<A>(x: A) -> A:
  return x

# Bool Negation
def not(x: Bool) -> Bool:
  if x:
    return False
  else:
    return True

# Type Negation
def Not(A: Set) -> Set:
  A -> Empty

# Nat Addition
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      return b
    case 1n + p:
      return 1n + add(p, b)

# Nat multiplication
def mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n + ap:
      return add(b, mul(ap, b))

# Nat Equality
def eql(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      return True
    case 1n+a 0n:
      return False
    case 0n 1n+b:
      return False
    case 1n+a 1n+b:
      return eql(a, b)

# List Map
def map<A,B>(f: A -> B, xs: A[]) -> B[]:
  match xs:
    case []:
      []
    case x <> xs:
      f(x) <> map<A,B>(f, xs)

# Custom Datatypes

type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>

def sum(tree: Tree<Nat>) -> Nat:
  match tree:
    case @Leaf{value}:
      return value
    case @Node{left, right}:
      return add(sum(left), sum(right))
  
# Inductive Types
# ---------------
# Bend uses equalities to emulate indices ("Fording")

type Vec<A: Set>(N: Nat):
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    h: A
    t: Vec(A,n)
    e: Nat{N == (1n+n)}

def head<A>(len: Nat, xs: Vec<A, (1n+len)>) -> A:
  match xs:
    case @Nil{e}:
      absurd e
    case @Cons{n, h, t, e}:
      return h

# Example Proofs
# --------------
# To illustrate the reasoning process, we document the GOAL at each step.

# a = a + 0
def zero_right(a: Nat) -> Nat{a == add(a,0n)}:
  match a:
    case 0n:
      # Nat{0n==0n}
      finally
    case 1n + ap:
      # Nat{1n+ap==1n+add(ap,0n)}
      1n + zero_right(ap)

# a + (1 + b) = 1 + (a + b)
def succ_right(a: Nat, b: Nat) -> Nat{add(a,1n+b) == (1n+add(a,b))}:
  match a:
    case 0n:
      # Nat{1n+b==1n+b}
      finally
    case 1n + ap:
      # Nat{1n+add(ap,1n+b)==1n+1n+add(ap,b)}
      1n + succ_right(ap,b)

# a + b = b + a
def comm(a: Nat, b: Nat) -> Nat{add(a,b) == add(b,a)}:
  match a:
    case 0n:
      # Nat{b==add(b,0n)}
      zero_right(b)
    case 1n+ap:
      # Nat{1n+add(ap,b)==add(b,1n+ap)}
      rewrite comm(ap,b)
      # Nat{1n+add(b,ap)==add(b,1n+ap)}
      rewrite succ_right(b,ap)
      # Nat{1n+add(b,ap)==1n+add(b,ap)}
      finally
