# Bend Syntax Reference

Bend has a Python-inspired syntax, Haskell-like semantics, and Lean-like type system.

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
0n       # Zero
123n     # Natural number literals
U64      # Unsigned Integer (64-bit)
I64      # Integer (64-bit)
F64      # Float (64-bit)
123      # U64 literal
+123     # I64 literal
123.0    # F64 literal
```

### Enums

```python
@{@A, @B, @C}   # Enum type
@Tag            # Enum value
```

### Compound Types

```python
T[]             # List of T
A -> B          # Function type (sugar for all _:A. B)
A & B           # Product type (sugar for any _:A. B)
all x:A. B      # Dependent function type (Πx:A. B)
all x:A y:B. C  # Multi-argument dependent function
any x:A. B      # Dependent pair type (Σx:A. B)
any x:A y:B. C  # Multi-argument dependent pair
T{a == b}       # Propositional Equality type
```

## Variables and Bindings

```python
x               # Variable
x = v           # Assignment (untyped)
x : T = v       # Assignment (typed)
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
- Linearizes a variable (useful on HVM target only)
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
(a, b)          # Tuples
(a, b, c)       # Nested tuples: (a, (b, c))
```

### Equality

```python
finally         # Reflexivity proof
```

## Type Annotations

```python
x :: T          # Type hint
```

## Simple Datatypes

Declaration:

```python
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A
```

Constructor:

```python
@None{}      # desugars to (@None,())
@Some{value} # desugars to (@Some,value,())
```

Pattern-Matching:

```python
match x:
  case @None{}:
    ...
  case @Some{value}:
    ...
```

## Inductive Datatypes

Declaration:

```python
# Same as:
# data Vec (A : Set) : Nat → Set where
#   nil  : Vec A zero
#   cons : ∀ {n} → A → Vec A n → Vec A (suc n)
type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0}
  case @Cons:
    n: Nat
    h: A
    t: Vec(A, n)
    e: Nat{N == 1+n}
```

This desugars to a function that returns a dependent pair:
- First component: an enum tag (@Nil or @Cons)
- Second component: a record of fields based on the constructor

Constructor:

```python
@Cons{head,tail} # desugars to (@Cons,head,tail,())
```

You can also pattern-match as usual.

## Imports

Bend automatically imports definitions from corresponding file names.

For example, in the file:

```python
def main() -> Nat:
  Foo/bar(123)
```

Bend will automatically import `Foo/bar` from one of:
- `./Foo/bar.bend`
- `./Foo/bar/_.bend`

# Inference

Bend has no inference. That means every polymorphic application must be explicit. Example:

```python
List/map<Char,Char>("foo", fn)
```

The explicit `<Char,Char>` specialization is mandatory.

# Examples

## Basic Programming

```python
def Nat/add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + Nat/add(p, b)

def Nat/mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n + p:
      Nat/add(b, Nat/mul(p, b))

def List/append<A>(xs: A[], ys: A[]) -> A[]:
  match xs:
    case []:
      ys
    case x <> xs:
      x <> List/append<A>(xs, ys)

def List/map<A,B>(xs: A[], f: A -> B) -> B[]:
  match xs:
    case []:
      []
    case x <> xs:
      f(x) <> List/map<A,B>(xs,f)

def List/fold<A>(xs: A[]) -> ∀P:Set. P -> (A -> P -> P) -> P:
  match xs:
    case []:
      lambda P nil cons.
      nil
    case x <> xs:
      lambda P nil cons.
      cons(x, List/fold(A,xs,P,nil,cons))
```

## Theorem Proving

```python
def Nat/add/zero_right(a: Nat) -> Nat{a == Nat/add(a,0n)}:
  match a:
    case 0n:
      finally
    case 1n + ap:
      1n + Nat/add/zero_right(ap)

def Nat/add/comm(a: Nat, b: Nat) -> Nat{Nat/add(a,b) == Nat/add(b,a)}:
  match a:
    case 0n:
      Nat/add/zero_right(b)
    case 1n+ap:
      rewrite Nat/add/comm(ap,b)
      rewrite Nat/add/succ_right(b,ap)
      finally
```
