# this gives the error

  # Unsupported pattern-match shape.
  # Support for it will be added in a future update.

# which is unhelpful because it does not point to the pattern location

type Bits:
  case @E:
  case @O:
    a: Bits
  case @I:
    b: Bits

def f(a: Bits, b: Bits) -> Nat:
  match a b:
    case a      @E{}:
      0n
    case @O{ap} @O{bp}:
      1n
    case @O{ap} @I{bp}:
      2n
    case @I{ap} @O{bp}:
      3n
    case @I{ap} @I{bp}:
      4n
