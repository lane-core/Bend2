# FIXME

# please implement a complete test program

###

# unfrk is generating incorrect duplications on shadowed names

  # λL. λx. λx. fork L: x else: x

# is converted before bind to

  # λL. λx. λx. ~ x { 
  #   &L{,}: λx0. λx1. ~ x { 
  #     &L{,}: λx0. λx1. &L{x0, x1}
  #   }
  # }
