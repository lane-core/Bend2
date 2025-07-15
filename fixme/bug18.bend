# FIXME

###

# explicit import with alias doesn't import
# works with the change inside f add => fixme/add_for_import

import fixme/add_for_import as add

def f() -> Nat -> Nat -> Nat:
  add

  # ✗ f
  # Undefined: add
  # Context:
  #
  # Location: (line 10, column 3)
  # 10 |   add
