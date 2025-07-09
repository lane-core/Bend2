# won't fix:
# def main(x: Nat) -> Nat: x def = 5n def
# is the same situation, is correct, and '=' is the first invalid token
# the situation below won't occur in practice as 'let' isn't used anymore

###

# this gives

  # PARSE_ERROR
  # unexpected '='
  # expecting letter or underscore
  #
  # At line 2, column 11:
  # 2 |   let def = 5n

# but the first nonsensical token is "def", not "="

def main() -> Nat: foo def = 5n def
