# FIXME

###

# very ugly error message:

  # ✗ check2
  # Mismatch:
  # - Goal: _ & _
  # - Type: (λ_. (λctr. ~ ctr { &Var: Σk:String. Σi:Nat. Unit ; &All: Σk:String. Σa:Term. Σb:Term -> Term. Unit ; &Lam: Σk:String. Σf:Term -> Term. Unit ; &Uni: Unit ; &Rwt: Unit ; λ_. () })(_x6))(&All)
  # Context:
  # - d : Nat
  # - ctx : Term[]
  # - term : Term
  # - goal : Term
  # - k : Char[]
  # - f : Term -> Term
  # Location: (line 57, column 11)
  # 57 |           match goal:
  # 58 |             case @All{g_k, a, b}: check2(1n+d, List/append<Term>(ctx, [a]), f(@Var{k, d}), b(@Var{g_k, d}))
  # 59 |             case _              : @None

# this example is quite large for debugging, but it's not obvious how to make a minimal version that reproduces it

type Term:
  case @Var: # x
    k: String
    i: Nat
  case @All: # ∀x:A.B
    k: String
    a: Term
    b: Term -> Term
  case @Lam: # λx.f
    k: String
    f: Term -> Term
  case @Uni:  # Unit
  case @Rwt:

type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

def String() -> Set:
  Char[]

def List/append<A>(xs: A[], ys: A[]) -> A[]:
  match xs:
    case []:
      ys
    case x <> xs:
      x <> List/append<A>(xs, ys)

# Returns the element at index i
def List/get<A>(xs: A[], i: Nat) -> Maybe<A>:
  match xs i:
    case [] 0n:
      return @None
    case (x <> xs) 0n:
      return @Some{x}
    case [] 1n+i:
      return @None
    case (x <> xs) 1n+i:
      return List/get<A>(xs, i)

def check2(d: Nat, ctx: Term[], term: Term, goal: Term) -> Maybe<Unit>:
  match goal:
    case @Rwt{}:
      @None
    case goal:
      match term:
        case @Lam{k, f}:
          match goal:
            case @All{g_k, a, b}: check2(1n+d, List/append<Term>(ctx, [a]), f(@Var{k, d}), b(@Var{g_k, d}))
            case _              : @None
        case @Var{k, i}:
          match List/get<Term>(ctx, i):
            case @Some{t}: @Some{()}
            case @None   : @None
        case _:
          @None

def main() -> Maybe<Unit>:
  x = @Lam{"x", λx. x}
  T = @All{"x", @Uni, λx. @Uni}
  check2(0n, [], x, T)
