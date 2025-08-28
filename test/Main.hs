module Main where

import Test
import System.Directory
import System.FilePath
import System.Process
import System.Exit
import System.Environment (getArgs)
import Control.Monad (forM_, when, filterM)
import Data.List (sort)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> runAllTests
    testNames -> runSpecificTests testNames

runAllTests :: IO ()
runAllTests = do
  testFiles <- findTestFiles "test/tests"
  
  if null testFiles
    then putStrLn "No test files found in test/tests/"
    else do
      results <- mapM runTestFile testFiles
      
      let passed = length $ filter id results
      let failed = length results - passed
      
      putStrLn ""
      putStrLn $ "Test summary: \x1b[32m" ++ show passed ++ " passed\x1b[0m, \x1b[31m" ++ show failed ++ " failed\x1b[0m"
      
      when (failed > 0) exitFailure

runSpecificTests :: [String] -> IO ()
runSpecificTests testNames = do
  let testFiles = map (\name -> if takeExtension name == ".hs" 
                                then "test/tests/" </> name
                                else "test/tests/" </> name <.> "hs") testNames
  
  existingFiles <- filterM doesFileExist testFiles
  let missingFiles = filter (`notElem` existingFiles) testFiles
  
  when (not $ null missingFiles) $ do
    putStrLn $ "Warning: Test files not found: " ++ show missingFiles
  
  if null existingFiles
    then putStrLn "No valid test files found"
    else do
      results <- mapM runTestFile existingFiles
      
      let passed = length $ filter id results
      let failed = length results - passed
      
      putStrLn ""
      putStrLn $ "Test summary: \x1b[32m" ++ show passed ++ " passed\x1b[0m, \x1b[31m" ++ show failed ++ " failed\x1b[0m"
      
      when (failed > 0) exitFailure

findTestFiles :: FilePath -> IO [FilePath]
findTestFiles dir = do
  exists <- doesDirectoryExist dir
  if not exists
    then return []
    else do
      entries <- listDirectory dir
      let fullPaths = map (dir </>) entries
      files <- filterM doesFileExist fullPaths
      let hsFiles = filter (\f -> takeExtension f == ".hs") files
      dirs <- filterM doesDirectoryExist fullPaths
      subFiles <- concat <$> mapM findTestFiles dirs
      return $ sort (hsFiles ++ subFiles)

runTestFile :: FilePath -> IO Bool
runTestFile file = do
  let testName = takeBaseName file
  (exitCode, out, err) <- readProcessWithExitCode "runhaskell" ["-i:test", file] ""
  
  case exitCode of
    ExitSuccess -> do
      putStrLn $ "\x1b[32m✓ " ++ testName ++ "\x1b[0m"
      -- Show the output indented
      when (not $ null out) $ putStr $ unlines $ map ("  " ++) $ lines out
      when (not $ null err) $ putStr $ unlines $ map ("  " ++) $ lines err
      return True
    ExitFailure n -> do
      putStrLn $ "\x1b[31m✗ " ++ testName ++ "\x1b[0m"
      -- Show the output indented
      when (not $ null out) $ putStr $ unlines $ map ("  " ++) $ lines out
      when (not $ null err) $ putStr $ unlines $ map ("  " ++) $ lines err
      return False
