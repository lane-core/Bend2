
def and(a: Bool, b: Bool) -> Bool:
  match a:
    case True:
      b
    case False:
      False

def and_assoc_theo(A: Bool, B: Bool, C: Bool) -> Bool{(and (and A B) C) == (and A (and B C))}:
  match A:
    case False:
      {==}
    case True:
      match B:
        case False:
          {==}
        case True:
          {==}

and_assoc_theo(False, False, False)
