{-# LANGUAGE MultilineStrings #-}

import Test

map_bend :: String
map_bend = """
def map<A,B>(f: A -> B, xs: A[]) -> B[]:
  match xs:
    case []:
      []
    case x <> xs:
      f(x) <> map<A,B>(f, xs)

def inc(x: Nat) -> Nat:
  1n + x

def plus2(x: Nat) -> Nat:
  2n + x

def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def T0 : Nat[]{[] == map<Nat,Nat>(inc, [])} = {==}
def T1 : Nat[]{[2n, 3n, 4n] == map<Nat,Nat>(inc, [1n, 2n, 3n])} = {==}
def T2 : Nat[]{[2n, 3n, 4n] == map<Nat,Nat>(plus2, [0n, 1n, 2n])} = {==}
def T3 : Bool[]{[False, True, False] == map<Bool,Bool>(neg, [True, False, True])} = {==}
"""

main :: IO ()
main = testFileChecks map_bend