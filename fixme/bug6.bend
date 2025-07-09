# FIXME

###

# this gives the error

  # IncompleteMatch:
  # Context:
  # - a : Bits
  # - b : Bits
  # - bp : Bits
  # Location: (line 9, column 3)
  #  9 |   match a b:
  # 10 |     case @E{}      a:
  # 11 |       @E{}
  # 12 |     case @O{bp} @O{ap}:
  # 13 |       @O{@E{}}
  # 14 |     case @I{bp} @O{ap}:
  # 15 |       @I{@E{}}
  # 16 |     case @O{bp} @I{ap}:
  # 17 |       @O{@I{@E{}}}
  # 18 |     case @I{bp} @I{ap}:
  # 19 |       @I{@I{@E{}}}

# which is misleading considering the error after the pattern is completed:

  # Unsupported pattern-match shape.
  # Support for it will be added in a future update.

type Bits:
  case @E:
  case @O:
    a: Bits
  case @I:
    b: Bits

def f(a: Bits, b: Bits) -> Bits:
  match a b:
    case @E{}      a:
      @E{}
    case a      @E{}:
      @E{}
    case @O{bp} @O{ap}:
      @O{@E{}}
    case @I{bp} @O{ap}:
      @I{@E{}}
    case @O{bp} @I{ap}:
      @O{@I{@E{}}}
    case @I{bp} @I{ap}:
      @I{@I{@E{}}}
