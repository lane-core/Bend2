
def and(x : Bool, y : Bool) -> Bool:
  match x:
    case True:
      y
    case False:
      False

def and_idemp_theo(x: Bool) -> Bool{and(x, x) == x}:
  match x:
    case False:
      {==}  # and(False, False) = False = False
    case True:
      {==}   # and(True, True) = True = True

and_idemp_theo(False)


