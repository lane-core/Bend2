# FIXME

###

# parser allows to do define gen(), while gen is a keyword
# notice the error is not at the definition of gen() as it should, but in main

  # PARSE_ERROR
  # unexpected '('
  # expecting letter or underscore
  # 
  # At line 11, column 6:
  # 11 |   gen()

def gen() -> Nat:
  0n

def main() -> Nat:
  123
