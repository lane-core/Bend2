# this gives the error:

  # PARSE_ERROR
  # reserved keyword 'def'
  #
  # At line 3, column 1:
  # 3 | def main() -> Unit:
  #     ^(marked here with color)

# it would be more helpful if there was
# a pointer to f, where the bug is actually address
#
# Ideally:

  # PARSE_ERROR
  # Function 'f' missing body
  #
  # At line 1, column 1:
  # 1 | def f() -> Unit:
  #                     ^(marked here)
  # Expected a function body after the signature.

def f(x: Nat) -> Unit:


def main() -> Unit:
  ()
