
def not(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def neg_impl_theo(x: Bool, y: Bool, e: Bool{not(x) == y}) -> Bool{not(y) == x}:
  match x y:
    with e
    case False False:
      e
    case False True:
      {==}
    case True False:
      {==}
    case True True:
      e

# not(True)
neg_impl_theo(False, True, {==})
