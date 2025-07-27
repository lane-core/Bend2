{-# LANGUAGE MultilineStrings #-}

import Test

eql_bend :: String
eql_bend = """
def eql(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n   0n  : True
    case 1n+a 0n  : False
    case 0n   1n+b: False
    case 1n+a 1n+b: eql(a, b)

def T0 : Bool{True == eql(0n, 0n)} = {==}
def T1 : Bool{False == eql(0n, 1n)} = {==}
def T2 : Bool{False == eql(1n, 0n)} = {==}
def T3 : Bool{True == eql(5n, 5n)} = {==}
"""

main :: IO ()
main = testFileChecks eql_bend
