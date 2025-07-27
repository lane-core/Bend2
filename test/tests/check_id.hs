{-# LANGUAGE MultilineStrings #-}

import Test

id_bend :: String
id_bend = """
def id<A>(x: A) -> A:
  x

def T0 : Nat{3n == id<Nat>(3n)} = {==}
def T1 : Bool{True == id<Bool>(True)} = {==}
def T2 : Nat{0n == id<Nat>(id<Nat>(0n))} = {==}
def T3 : Char[]{"hello" == id<Char[]>("hello")} = {==}
"""

main :: IO ()
main = testFileChecks id_bend
