def String() -> Set:
  Char[]

type Complex:
  case @A:
    f: (Nat -> Complex) -> Complex
  case @B:
    value: String

def Check(ctx: Complex[], x: Complex) -> Complex:
  match x:
    case @A{f}:
      # Type error: should return Complex but returns a function
      λg. f(g)
    case @B{value}:
      @B{value}

def main() -> Complex:
  ctx = [@B{"test"}]
  x = @A{λg. g(@B{"inner"})}
  Check(ctx, x)
