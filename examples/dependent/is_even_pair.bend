def is_even(a: Nat) -> Bit:
  switch a:
    case 0:
      True
    case 1+n:
      switch n:
        case 0:
          False
        case 1+n1:
          is_even(n1)

def test(a: Σ(n: Nat). is_even(n) == False : Bit) -> Bit:
  True

test((1, {=}))
