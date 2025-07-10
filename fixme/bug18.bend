# FIXME

###

# import alias gives the error:

  # Error: Definition 'add' not found. Expected file at: add.bend, add.bend.py, add/_.bend or add/_.bend.py

# no error would happen if we instead had the unaliased

  # def f() -> Nat -> Nat -> Nat:
  #   add_for_import

import add_for_import as add

def f() -> Nat -> Nat -> Nat:
  add

