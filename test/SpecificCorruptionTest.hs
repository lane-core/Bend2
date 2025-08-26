-- Specific test to trigger the known string concatenation corruption
{-# LANGUAGE ViewPatterns #-}

module SpecificCorruptionTest where

import Core.Type hiding (noSpan, collectVars)
import Core.Adjust.FlattenPats
import Core.Show
import Data.List (nub, isInfixOf)

-- Test configuration
noSpan :: Span
noSpan = Span (0,0) (0,0) "" ""

emptyBook :: Book  
emptyBook = Book mempty []

-- This should trigger the (Con _ _, Var k _) case on line 188
corruptionTriggerTest :: Term
corruptionTriggerTest = Pat [Var "x" 0] [] [([Con (Var "h" 0) (Var "t" 0)], Var "h" 0)]

main :: IO ()
main = do
  putStrLn "=== Specific Corruption Test ==="
  putStrLn "This should trigger string concatenation (k++\"h\") bug"
  putStrLn ""
  
  let original = corruptionTriggerTest
  putStrLn $ "Original pattern: " ++ show original
  
  let flattened = flattenPats 0 noSpan emptyBook original
  putStrLn $ "Flattened result: " ++ show flattened
  
  -- Look for the specific corruption pattern
  let vars = extractAllVarNames flattened
  putStrLn $ "All variable names found: " ++ show vars
  
  -- Check for string concatenation corruption (should find "hh", "ht" etc.)
  let hasStringConcat = any (looksLikeStringConcat) vars
  putStrLn $ "Has string concatenation corruption: " ++ show hasStringConcat
  
  if hasStringConcat then
    putStrLn "✗ CORRUPTION DETECTED - This is the bug we need to fix!"
  else
    putStrLn "✓ No corruption found - either already fixed or test needs adjustment"

-- Extract all variable names from a term
extractAllVarNames :: Term -> [String] 
extractAllVarNames term = case term of
  Var name _ -> [name]
  Pat scrutinees moves cases ->
    concatMap extractAllVarNames scrutinees ++
    concatMap (extractAllVarNames . snd) moves ++
    concatMap (\(patterns, body) -> concatMap extractAllVarNames patterns ++ extractAllVarNames body) cases
  Con h t -> extractAllVarNames h ++ extractAllVarNames t
  Tup a b -> extractAllVarNames a ++ extractAllVarNames b
  App f x -> extractAllVarNames f ++ extractAllVarNames x
  Lam _ _ f -> extractAllVarNames (f (Var "dummy" 0))
  _ -> []  -- Add more cases as needed

-- Detect string concatenation pattern
looksLikeStringConcat :: String -> Bool
looksLikeStringConcat name = 
  (any (`isInfixOf` name) ["h", "t", "x", "y", "a", "b"]) && 
  length name > 1 &&
  not (name `elem` ["h", "t", "x", "y", "a", "b"])  -- Exclude single-char names