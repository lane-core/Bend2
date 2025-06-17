def and2(a: Bool, b: Bool) -> Bool:
  match a b:
    case True  True :
      True
    case False _    :
      False
    case _     False:
      False

and2(True, False)
