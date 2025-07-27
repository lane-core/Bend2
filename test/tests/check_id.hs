{-# LANGUAGE MultilineStrings #-}

import Test

id_bend :: String
id_bend = """
def id<A>(x: A) -> A:
  x

assert 3n == id<Nat>(3n) : Nat
assert True == id<Bool>(True) : Bool
assert 0n == id<Nat>(id<Nat>(0n)) : Nat
assert "hello" == id<Char[]>("hello") : Char[]
"""

main :: IO ()
main = testFileChecks id_bend
