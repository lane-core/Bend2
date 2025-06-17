
def bit_cnot(a: Bool, b: Bool) -> Bool:
  match a b:
    case True True:
      False
    case True False:
      True
    case False True:
      True
    case False f:
      f

bit_cnot(False, False)
