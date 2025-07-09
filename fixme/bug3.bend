# this gives

  # PARSE_ERROR
  # unexpected '='
  # expecting letter or underscore
  #
  # At line 2, column 11:
  # 2 |   let def = 5n

# but the first nonsensical token is "def", not "="

def main() -> Nat:
  let def = 5n
  def
