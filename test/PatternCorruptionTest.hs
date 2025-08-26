-- Test for Pattern Variable Corruption Fix
-- ========================================
-- This test validates that pattern flattening generates proper fresh variables
-- instead of using string concatenation which violates scoping invariants.

{-# LANGUAGE ViewPatterns #-}

module PatternCorruptionTest where

import Core.Type hiding (noSpan, collectVars)
import Core.Adjust.FlattenPats
import Core.Show
import Data.List (nub, isInfixOf, (\\))

-- Test configuration
noSpan :: Span
noSpan = Span (0,0) (0,0) "" ""

emptyBook :: Book  
emptyBook = Book mempty []

-- Test case definitions
testCase1 :: Term
testCase1 = Pat [Var "myList" 0] [] [([Con (Var "x" 0) (Var "xs" 0)], Var "x" 0)]

testCase2 :: Term  
testCase2 = Pat [Var "pair" 0] [] [([Tup (Var "a" 0) (Var "b" 0)], Var "a" 0)]

testCase3 :: Term
testCase3 = Pat [Var "sup" 0] [] [([Sup (Var "label" 0) (Var "x" 0) (Var "y" 0)], Var "x" 0)]

-- Nested pattern test
testCase4 :: Term
testCase4 = Pat [Var "nested" 0] [] [([Con (Con (Var "a" 0) (Var "b" 0)) (Var "rest" 0)], Var "a" 0)]

-- Variable analysis functions
collectVars :: Term -> [(String, Int)]
collectVars = collectVarsHelper
  where 
    collectVarsHelper t = case t of
      Var k i -> [(k, i)]
      Ref k i -> []
      Sub t -> collectVarsHelper t
      Fix k f -> collectVarsHelper (f (Var k 0))
      Let k t v f -> maybe [] collectVarsHelper t ++ collectVarsHelper v ++ collectVarsHelper (f (Var k 0))
      Use k v f -> collectVarsHelper v ++ collectVarsHelper (f (Var k 0))
      Chk x t -> collectVarsHelper x ++ collectVarsHelper t
      Tst x -> collectVarsHelper x
      UniM f -> collectVarsHelper f
      BitM f t -> collectVarsHelper f ++ collectVarsHelper t
      NatM z s -> collectVarsHelper z ++ collectVarsHelper s
      Lst t -> collectVarsHelper t
      Con h t -> collectVarsHelper h ++ collectVarsHelper t
      LstM n c -> collectVarsHelper n ++ collectVarsHelper c
      EnuM cs d -> concatMap (collectVarsHelper . snd) cs ++ collectVarsHelper d
      Op2 _ a b -> collectVarsHelper a ++ collectVarsHelper b
      Op1 _ a -> collectVarsHelper a
      Sig t f -> collectVarsHelper t ++ collectVarsHelper f
      Tup a b -> collectVarsHelper a ++ collectVarsHelper b
      SigM f -> collectVarsHelper f
      All t f -> collectVarsHelper t ++ collectVarsHelper f
      Lam k t f -> maybe [] collectVarsHelper t ++ collectVarsHelper (f (Var k 0))
      App f a -> collectVarsHelper f ++ collectVarsHelper a
      Eql t a b -> collectVarsHelper t ++ collectVarsHelper a ++ collectVarsHelper b
      EqlM f -> collectVarsHelper f
      Rwt e f -> collectVarsHelper e ++ collectVarsHelper f
      Met n t ctx -> collectVarsHelper t ++ concatMap collectVarsHelper ctx
      Sup l a b -> collectVarsHelper l ++ collectVarsHelper a ++ collectVarsHelper b
      SupM l f -> collectVarsHelper l ++ collectVarsHelper f
      Loc _ t -> collectVarsHelper t
      Log s x -> collectVarsHelper s ++ collectVarsHelper x
      Pat ts ms cs -> concatMap collectVarsHelper ts ++ concatMap (collectVarsHelper . snd) ms ++ 
                      concatMap (\(ps, t) -> concatMap collectVarsHelper ps ++ collectVarsHelper t) cs
      Frk l a b -> collectVarsHelper l ++ collectVarsHelper a ++ collectVarsHelper b
      _ -> []

-- Corruption detection  
detectStringConcatCorruption :: [String] -> [String]
detectStringConcatCorruption varNames = 
  filter hasCorruptionPattern varNames
  where
    hasCorruptionPattern name = any (`isInfixOf` name) corruptionSuffixes && 
                               not (name `elem` standardNames)
    corruptionSuffixes = ["h", "t", "x", "y", "a", "b"]
    standardNames = ["h", "t", "x", "y", "a", "b", "_", "k"]  -- Allow these as user names

-- Fresh variable detection
detectFreshVars :: [String] -> [String] 
detectFreshVars varNames = filter isFreshVar varNames
  where isFreshVar name = "_x" `isInfixOf` name

-- Test individual pattern
testPattern :: String -> Term -> IO ()
testPattern name pattern = do
  putStrLn $ "\n=== Testing " ++ name ++ " ==="
  putStrLn $ "Original: " ++ show pattern
  
  let flattened = flattenPats 0 noSpan emptyBook pattern
  putStrLn $ "Flattened: " ++ show flattened
  
  let vars = collectVars flattened
  let varNames = map fst vars
  putStrLn $ "Variables: " ++ show vars
  
  let corrupted = detectStringConcatCorruption varNames
  let fresh = detectFreshVars varNames
  let duplicates = varNames \\ nub varNames
  
  putStrLn $ "Corrupted variables: " ++ show corrupted
  putStrLn $ "Fresh variables: " ++ show fresh  
  putStrLn $ "Duplicate variables: " ++ show duplicates
  
  -- Success criteria
  let success = null corrupted && null duplicates
  putStrLn $ if success then "✓ PASS" else "✗ FAIL"

-- Run all tests
runTests :: IO ()
runTests = do
  putStrLn "Pattern Corruption Test Suite"
  putStrLn "==============================="
  
  testPattern "List Pattern" testCase1
  testPattern "Tuple Pattern" testCase2  
  testPattern "Superposition Pattern" testCase3
  testPattern "Nested Pattern" testCase4
  
  putStrLn "\n=== Summary ==="
  putStrLn "Before fix: Should show corrupted variables with string concatenation"
  putStrLn "After fix: Should show fresh variables with _x{n} naming"

main :: IO ()
main = runTests