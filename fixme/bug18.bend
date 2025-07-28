# FIXME

# fixed:
# aliasing logic was not removing the '/' suffix, which caused refs to be unavailable
# errors were not being handled very good.
#  1. Parses the import and stores "add/" => "fixme/add_for_import/"
#  2. When parsing add, checks for exact match: M.lookup "add/" finds "fixme/add_for_import/"
#  3. Strips the trailing "/" to get "fixme/add_for_import"
#  4. Auto-import system loads the definition from fixme/add_for_import.bend

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
