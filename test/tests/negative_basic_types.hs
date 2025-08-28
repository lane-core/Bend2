{-# LANGUAGE MultilineStrings #-}

import Test

-- Test basic type mismatches that our intrinsic checker should catch
bool_nat_mismatch_bend :: String
bool_nat_mismatch_bend = """
def main : Nat = True
"""

nat_bool_mismatch_bend :: String
nat_bool_mismatch_bend = """
def main : Bool = 0n
"""

nat_suc_bool_mismatch_bend :: String
nat_suc_bool_mismatch_bend = """
def main : Bool = 1n
"""

bool_false_nat_mismatch_bend :: String
bool_false_nat_mismatch_bend = """
def main : Nat = False
"""

main :: IO ()
main = do
  putStrLn "🧪 Testing basic type mismatches with intrinsic checker..."
  
  -- Test 1: Bool where Nat expected
  testFile bool_nat_mismatch_bend "Bool as Nat should fail" $ \out err -> do
    if "Mismatch" `isInfixOf` err || "Type mismatch" `isInfixOf` err
      then putStrLn "✅ Bool->Nat mismatch correctly detected"
      else putStrLn "❌ Bool->Nat mismatch not caught"
  
  -- Test 2: Nat where Bool expected  
  testFile nat_bool_mismatch_bend "Nat as Bool should fail" $ \out err -> do
    if "Mismatch" `isInfixOf` err || "Type mismatch" `isInfixOf` err
      then putStrLn "✅ Nat->Bool mismatch correctly detected"
      else putStrLn "❌ Nat->Bool mismatch not caught"
      
  -- Test 3: Suc Nat where Bool expected
  testFile nat_suc_bool_mismatch_bend "Suc Nat as Bool should fail" $ \out err -> do
    if "Mismatch" `isInfixOf` err || "Type mismatch" `isInfixOf` err
      then putStrLn "✅ Suc Nat->Bool mismatch correctly detected"
      else putStrLn "❌ Suc Nat->Bool mismatch not caught"
      
  -- Test 4: False where Nat expected
  testFile bool_false_nat_mismatch_bend "False as Nat should fail" $ \out err -> do
    if "Mismatch" `isInfixOf` err || "Type mismatch" `isInfixOf` err
      then putStrLn "✅ False->Nat mismatch correctly detected"
      else putStrLn "❌ False->Nat mismatch not caught"

isInfixOf :: String -> String -> Bool
isInfixOf needle haystack = needle `elem` words haystack || any (needle `isInfixOf`) (tails haystack)
  where
    tails [] = []
    tails xs@(_:ys) = xs : tails ys