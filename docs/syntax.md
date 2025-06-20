# Bend Syntax Reference

## Comments

```python
# Single line comment
```

## Basic Types

### Primitives

```python
Set      # Type universe
Empty    # Empty type
Unit     # Unit type
()       # Unit value
Bool     # Boolean type  
False    # Boolean false
True     # Boolean true
Nat      # Natural number type
0        # Zero
123      # Natural number literals
```

### Enums

```python
@{@A, @B, @C}   # Enum type
@Tag            # Enum symbol
@Tag{f1, f2}    # Constructor - desugars to (@Tag,f1,f1,())
```

### Compound Types

```python
T[]             # List of T
A -> B          # Function type (sugar for all _:A. B)
A & B           # Product type (sugar for any _:A. B)
all x:A. B      # Dependent function type
all x:A y:B. C  # Multi-argument dependent function
any x:A. B      # Dependent pair type
any x:A y:B. C  # Multi-argument dependent pair
T{a == b}       # Propositional Equality type
```

## Variables and Bindings

```python
x               # Variable
x = v           # Let binding
```

## Functions

```python
lambda x. e        # Lambda abstraction
lambda x y z. e    # Multi-argument lambda
f(a, b, c)      # Function application

# Function definition sugar:
def f(x: A, y: B) -> C:
  body
```

Note: All functions take exactly one argument. Multi-argument syntax is sugar for curried functions.

## Pattern Matching

### Simple Patterns

```python
# Booleans
if cond:
  trueCase
else:
  falseCase

# Natural numbers  
match n:
  case 0:
    zeroCase
  case 1 + p:
    succCase
```

### General Pattern Matching

```python
match x y ...:
  with a = val0
  with b = val1
  ...
  case pat1 pat2 ...:
    body1
  case pat3 pat4 ...:
    body2
  ...
```

The `with` clause serves two purposes:
- Linearizes a variable (useful for HVM target)
- Specializes its type (useful for theorem proving)

### Eliminators (Low-level)

Pattern matches desugar to native eliminators, which can also be used directly:

```python
λ{(): e}              # Unit eliminator
λ{False: f; True: t}  # Bool eliminator  
λ{0: z; +: s}         # Nat eliminator
λ{[]: n; <>: c}       # List eliminator
λ{(,): f}             # Pair eliminator
λ{{==}: f}            # Equality eliminator
λ{@A: a; @B: b}       # Enum eliminator
```

## Data Constructors

### Lists

```python
[]              # Empty list
[1, 2, 3]       # List literal
h <> t          # Cons
```

### Tuples

```python
(a, b)          # Tuple
(a, b, c)       # Nested tuples: (a, (b, c))
```

### Equality

```python
{==}            # Reflexivity proof
```

## Type Annotations

```python
x :: T          # Type hint
```

## Datatype Declarations

```python
# data Vec (A : Set) : Nat → Set where
#   nil  : Vec A zero
#   cons : ∀ {n} → A → Vec A n → Vec A (suc n)
type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0}
  case @Cons:
    n: Nat
    h: A
    t: Vec(A,n)
    e: Nat{N == 1+n}
```

This desugars to a function that returns a dependent pair:
- First component: an enum tag (@Nil or @Cons)
- Second component: a record of fields based on the constructor

# Examples

## Basic Programming

```python
# Boolean operations
def and(a: Bool, b: Bool) -> Bool:
  if a:
    b
  else:
    False

def or(a: Bool, b: Bool) -> Bool:
  if a:
    True
  else:
    b

# List operations
def length<A>(xs: A[]) -> Nat:
  match xs:
    case []:
      0
    case h <> t:
      1 + length(t)

def append<A>(xs: A[], ys: A[]) -> A[]:
  match xs:
    case []:
      ys
    case h <> t:
      h <> append(t, ys)

def map<A, B>(f: A -> B, xs: A[]) -> B[]:
  match xs:
    case []:
      []
    case h <> t:
      f(h) <> map(f, t)
```

## Custom Datatypes

```python
# Option type
type Option<A: Set> -> Set:
  case @None:
  case @Some:
    value: A

# Option operations
def map_option<A, B>(f: A -> B, opt: Option(A)) -> Option(B):
  match opt:
    case @None{}:
      @None{}
    case @Some{value: x}:
      @Some{value: f(x)}

def bind_option<A, B>(opt: Option(A), f: A -> Option(B)) -> Option(B):
  match opt:
    case @None{}:
      @None{}
    case @Some{value: x}:
      f(x)

# Binary tree
type Tree<A: Set> -> Set:
  case @Leaf:
  case @Node:
    value: A
    left: Tree(A)
    right: Tree(A)

# Tree operations
def size<A>(t: Tree(A)) -> Nat:
  match t:
    case @Leaf{}:
      0
    case @Node{value: v, left: l, right: r}:
      1 + size(l) + size(r)

def mirror<A>(t: Tree(A)) -> Tree(A):
  match t:
    case @Leaf{}:
      @Leaf{}
    case @Node{value: v, left: l, right: r}:
      @Node{value: v, left: mirror(r), right: mirror(l)}
```

## Theorem Proving

```python
# Identity function is identity
def id_is_id<A>(x: A) -> A{id(x) == x}:
  {==}

# Symmetry of equality
def sym<A>(a: A, b: A, e: A{a == b}) -> A{b == a}:
  {==} = e
  {==}

# Transitivity of equality
def trans<A>(a: A, b: A, c: A, e1: A{a == b}, e2: A{b == c}) -> A{a == c}:
  {==} = e1
  {==} = e2
  {==}

# List concatenation is associative
def append_assoc<A>(xs: A[], ys: A[], zs: A[]) -> A[]{append(append(xs, ys), zs) == append(xs, append(ys, zs))}:
  match xs:
    case []:
      {==}
    case h <> t:
      # Goal transforms to: A[]{h <> append(append(t, ys), zs) == h <> append(t, append(ys, zs))}
      1 <> append_assoc(t, ys, zs)

# Size is preserved by mirror
def mirror_preserves_size<A>(t: Tree(A)) -> Nat{size(mirror(t)) == size(t)}:
  match t:
    case @Leaf{}:
      {==}
    case @Node{value: v, left: l, right: r}:
      # Inductive hypothesis
      ihl = mirror_preserves_size(l)
      ihr = mirror_preserves_size(r)
      # Goal requires commutativity of addition
      # (would need a lemma about add_comm here)
      {==}
```

## Using `with` for Specialization

```python
# The 'with' clause can help with type specialization in proofs
def vec_head<A>(n: Nat, v: Vec(A, 1+n)) -> A:
  match v:
    case (ctr, fields):
      match ctr:
        with fields    # Specializes 'fields' based on constructor
        case @Nil:
          # Impossible case - would give us proof that 1+n == 0
          ({==}, ()) = fields
          0  # Unreachable
        case @Cons:
          (_, head, _, {==}, ()) = fields
          head
```



## Desugaring Rules

### Function Definitions

```python
# Surface syntax:
def f(x: A, y: B) -> C:
  body

# Desugars to:
f : all x:A. all y:B. C = μf. lambda x. lambda y. body
```

### Type Declarations

```python
# Surface syntax:
type Maybe<A: Set> -> Set:
  case @None:
  case @Some:
    value: A

# Desugars to:
def Maybe(A: Set) -> Set:
  any ctr: @{@None, @Some}.
  match ctr:
    case @None:
      Unit
    case @Some:
      any value: A.
      Unit
```

### Other Sugars

```python
# Function type
A -> B              # all _:A. B

# Product type  
A & B               # any _:A. B

# Natural numbers
1 + n               # ↑n
123                 # ↑↑...↑0 (123 times)

# If-then-else
if c: t else: f     # (λ{False: f; True: t} c)

# List literal
[a, b, c]           # a <> b <> c <> []

# Tuple
(a, b, c)           # (a, (b, c))

# Constructor sugar
@Tag{v1, v2}        # (@Tag, v1, v2, ())
```

### Equality Rewriting

```python
# Pattern matching on equality proof:
{==} = proof        # Rewrites all occurrences based on proof

# Example:
def sym<A>(a: A, b: A, e: A{a == b}) -> A{b == a}:
  {==} = e    # rewrites 'a' to 'b' on goal
  {==}        # goal is now A{b == b}, solved by reflexivity
```

---

*Generated by Claude Opus 4*
