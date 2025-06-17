
def length(A: Set, xs: A[]) -> Nat:
  match xs:
    case []:
      0
    case h <> t:
      1 + length(A, t)

def append(A: Set, a: A[], b: A[]) -> A[]:
  match a:
    case []:
      b
    case aH<>aT:
      aH<>append(A, aT, b)

def add(n: Nat, y: Nat) -> Nat:
  match n:
    case 0:
      y
    case 1+nP:
      1+add(nP, y)

# Congruence of equality
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  match e:
    case {==}:
      {==}

# length(Nat, [1, 2])
# append(Nat, [1, 2], [3, 4])

def length_append_theo(A: Set, xs: A[], ys: A[]) -> Nat{length(A, append(A, xs, ys)) == add(length(A, xs), length(A, ys))}:
  match xs:
    case []:
      {==}
    case x <> xs:
      let ind = length_append_theo(A, xs, ys)
      cong(Nat, Nat, length(A, append(A, xs, ys)), add(length(A, xs), length(A, ys)), λx.↑x, ind)

length_append_theo(Nat, [1, 2, 3], [4, 5, 6])

