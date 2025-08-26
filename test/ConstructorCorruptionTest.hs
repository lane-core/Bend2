-- Test to force constructor pattern compilation and trigger string concatenation corruption
{-# LANGUAGE ViewPatterns #-}

module ConstructorCorruptionTest where

import Core.Type hiding (noSpan, collectVars)
import Core.Adjust.FlattenPats
import Core.Show

-- Test configuration
noSpan :: Span
noSpan = Span (0,0) (0,0) "" ""

emptyBook :: Book  
emptyBook = Book mempty []

-- Test case designed to trigger peelCtrCol with (Con _ _, Var k _) 
-- This should force the constructor flattening path
triggerCorruption :: Term
triggerCorruption = Pat 
  [Var "list" 0]  -- scrutinee 
  []              -- no moves
  [( [Con (Var "head" 0) (Var "tail" 0)]  -- pattern with constructor 
   , Var "head" 0  -- body
   )]

-- Even more specific test - this should definitely trigger the corruption
-- It creates a pattern where we have a variable being matched against a constructor
forceCorruption :: Term  
forceCorruption = Pat
  [Var "xs" 0]    -- scrutinee
  []              -- no moves  
  [( [Var "x" 0]  -- first case: variable pattern  
   , Var "x" 0    -- body
   ),
   ( [Con (Var "h" 0) (Var "t" 0)]  -- second case: constructor pattern
   , Var "h" 0     -- body  
   )]

main :: IO ()
main = do
  putStrLn "=== Constructor Corruption Test ==="
  putStrLn ""
  
  putStrLn "Test 1: Constructor pattern"
  let test1 = triggerCorruption
  putStrLn $ "Original: " ++ show test1
  let flattened1 = flattenPats 0 noSpan emptyBook test1
  putStrLn $ "Flattened: " ++ show flattened1
  
  putStrLn ""
  putStrLn "Test 2: Mixed variable/constructor patterns"  
  let test2 = forceCorruption
  putStrLn $ "Original: " ++ show test2
  let flattened2 = flattenPats 0 noSpan emptyBook test2
  putStrLn $ "Flattened: " ++ show flattened2
  
  -- Check for the specific corruption we're looking for
  let vars1 = extractVarNames flattened1
  let vars2 = extractVarNames flattened2  
  
  putStrLn ""
  putStrLn $ "Variables in test 1: " ++ show vars1
  putStrLn $ "Variables in test 2: " ++ show vars2
  
  let corruption1 = filter hasCorruptionPattern vars1
  let corruption2 = filter hasCorruptionPattern vars2
  
  putStrLn $ "Corruption in test 1: " ++ show corruption1
  putStrLn $ "Corruption in test 2: " ++ show corruption2

extractVarNames :: Term -> [String]
extractVarNames (Var name _) = [name]
extractVarNames (Pat scruts moves cases) = 
  concatMap extractVarNames scruts ++
  concatMap (extractVarNames . snd) moves ++
  concatMap (\(ps, body) -> concatMap extractVarNames ps ++ extractVarNames body) cases
extractVarNames (Con a b) = extractVarNames a ++ extractVarNames b
extractVarNames (Tup a b) = extractVarNames a ++ extractVarNames b  
extractVarNames (App f x) = extractVarNames f ++ extractVarNames x
extractVarNames (Lam _ _ f) = extractVarNames (f (Var "_dummy" 0))
extractVarNames _ = []

-- Look for the specific string concatenation patterns we expect
hasCorruptionPattern :: String -> Bool  
hasCorruptionPattern name = name `elem` expectedCorruptions
  where
    expectedCorruptions = 
      [ "xh", "xt"     -- x + "h", x + "t" 
      , "headh", "headt" -- head + "h", head + "t"
      , "hh", "ht"     -- h + "h", h + "t" 
      , "th", "tt"     -- t + "h", t + "t"
      ]