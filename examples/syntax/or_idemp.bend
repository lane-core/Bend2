
def or(x : Bool, y : Bool) -> Bool:
  if x:
    True
  else:
    y

def or_idemp_theo(x: Bool) -> Bool{or(x, x) == x}:
  match x:
    case False:
      {==} 
    case True:
      {==}

or_idemp_theo(False)
