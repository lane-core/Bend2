{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit 91c8924cffc7f476c8925fffb7e10bf1642be5b3
--
-- fixed. parseTermBefore should restore the blocked ops always
-- even when its internal parseTerm fails. with this, additional
-- parseTermBefore have to be used e.g. in parsing 'case ...:`
--
-- BUG DESCRIPTION:
-- when used under the combinator 'some',
-- parseTermBefore "op" is not reseting the block list
-- causing ":" to be blocked beyond where it was intended to

parsed_op_not_reset_blocklist :: String
parsed_op_not_reset_blocklist = """
def f(a:Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      1n

def g() -> Nat:
  a = 0n :: Nat
  a

  # PARSE_ERROR
  # unexpected ":: Nat<newline>"
  # expecting "def", "import", "type", '(', ';', Eraser, absurd, character literal, dependent function type, dependent pair type, empty list ([]), end of input, enum symbol / constructor, enum type, fixed point, fork, if clause, lambda abstraction, list literal, log, natural number literal, natural number type (Nat), numeric literal, numeric unary operation, pattern match, reflexivity ({==} or finally), return statement, rewrite, string literal, superposition, tilde expression (induction or match), unit value (()), variable, or view
  #
  # At line 9, column 10:
  # 9 |   a = 0n :: Nat
"""

main :: IO ()
main = testFileChecks parsed_op_not_reset_blocklist
