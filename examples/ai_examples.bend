# Bend has:
# - Python-like syntax
# - Haskell-like evaluation
# - Lean-like types

# Native Types
# ------------

# - Empty         ::=                  -- empty
# - Unit          ::= ()               -- unit
# - Bool          ::= True, False      -- boolean
# - Nat           ::= 0n, 1n+pred      -- natural number
# - List(T)       ::= [], head <> tail -- linked list
# - @{@A,@B,...}  ::= @A, @B, ...      -- inline enum
# - any x:A. B(x) ::= (x, y)           -- dependent pair
# - all x:A. B(x) ::= λx. f(x)         -- dependent func
# - T{a == b}     ::= finally          -- identity

# Example Functions
# -----------------

# Bool Negation
def not(x: Bool) -> Bool:
  if x:
    return False
  else:
    return True

# Nat Predecessor
def pred(a: Nat) -> Nat:
  match a:
    case 0n:
      return 0n
    case 1n + p:
      return p

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
      return 0n
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
      return []
    case x <> xs:
      head = f(x)
      tail = map<A,B>(f, xs)
      return head <> tail

# List Fold
def fold<A,B>(f: A -> B -> B, a: B, xs: A[]) -> B:
  match xs:
    case []:
      return a
    case x <> xs:
      return f(x, fold<A,B>(f, a, xs))

# Custom Datatypes
# ----------------

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
      sl = sum(left)
      sr = sum(right)
      return add(sl, sr)
  
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
# To illustrate the reasoning, document the GOAL on each step.

# a = b → f(a) = f(b)
def app<A,B>(a: A, b: A, f: A -> B, e: A{a == b}) -> B{f(a) == f(b)}:
  # B{f(a)==f(b)}
  rewrite e
  # B{f(b)==f(b)}
  finally

# a = a + 0
def add_zero_right(a: Nat) -> Nat{a == add(a,0n)}:
  match a:
    case 0n:
      # Nat{0n==0n}
      finally
    case 1n + ap:
      # Nat{1n+ap==1n+add(ap,0n)}
      return 1n + add_zero_right(ap)

# a + (1 + b) = 1 + (a + b)
def add_succ_right(a: Nat, b: Nat) -> Nat{add(a,1n+b) == (1n+add(a,b))}:
  match a:
    case 0n:
      # Nat{1n+b==1n+b}
      finally
    case 1n + ap:
      # Nat{1n+add(ap,1n+b)==1n+1n+add(ap,b)}
      return 1n + add_succ_right(ap,b)

# a + b = b + a
def add_comm(a: Nat, b: Nat) -> Nat{add(a,b) == add(b,a)}:
  match a:
    case 0n:
      # Nat{b==add(b,0n)}
      return add_zero_right(b)
    case 1n+ap:
      # Nat{1n+add(ap,b)==add(b,1n+ap)}
      rewrite add_comm(ap,b)
      # Nat{1n+add(b,ap)==add(b,1n+ap)}
      rewrite add_succ_right(b,ap)
      # Nat{1n+add(b,ap)==1n+add(b,ap)}
      finally

# 1n + n = 1n + m → n = m
def succ_inj(n: Nat, m: Nat, e: Nat{(1n+n)==(1n+m)}) -> Nat{n==m}:
  match n m e:
    case 0n 0n e:
      # Nat{0n==0n}
      finally
    case 1n+n 0n e:
      # Nat{1n+n==0n}
      absurd e
    case 0n 1n+m e:
      # Nat{0n==1n+m}
      absurd e
    case 1n+n 1n+m e:
      # Nat{1n+n==1n+m}
      return app<Nat,Nat>(1n+1n+n, 1n+1n+m, pred, e)
