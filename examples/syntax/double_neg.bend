# Negation on booleans
# - not(True)  = False
# - not(False) = True
def not(x: Bool) -> Bool:
  match x:
    case False:
      True
    case True:
      False

def double_neg_theo(x: Bool) -> Bool{not(not(x)) == x}:
  match x:
    case False:
      {==}
    case True:
      {==}

double_neg_theo(False)

