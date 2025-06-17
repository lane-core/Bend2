
def not(a: Bool) -> Bool:
  match a:
    case False:
      True
    case True:
      False

def and(a: Bool, b: Bool) -> Bool:
  match a:
    case False:
      False
    case True:
      b

def or(a: Bool, b: Bool) -> Bool:
  match a:
    case False:
      match b:
        case False:
          False
        case True:
          True
    case True:
      True

def de_morgan_theo(A: Bool, B: Bool) -> Bool{(not (and A B)) == (or (not A) (not B))}:
  match A:
    case False:
      {==}  # Left:  not(False AND B) = not(False) = True
           # Right: or(not(False), not(B)) = or(True, not(B)) = True
    case True:
      match B:
        case False:
          {==}  # Left:  not(True AND False) = not(False) = True
               # Right: or(not(True), not(False)) = or(False, True) = True
        case True:
          {==}  # Left:  not(True AND True) = not(True) = False
               # Right: or(not(True), not(True)) = or(False, False) = False

de_morgan_theo(True, False)

