module Main where

import Test
import System.Directory
import System.FilePath
import System.Process
import System.Exit
import Control.Monad (forM_, when, filterM)
import Data.List (sort)

main :: IO ()
main = do
  testFiles <- findTestFiles "test/tests"
  
  if null testFiles
    then putStrLn "No test files found in test/tests/"
    else do
      results <- mapM runTestFile testFiles
      
      let passed = length $ filter id results
      let failed = length results - passed
      
      putStrLn ""
      putStrLn $ "\ESC[1mTest summary: " ++ show passed ++ " passed, " ++ show failed ++ " failed\ESC[0m"
      
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
  putStrLn $ "\ESC[1m> " ++ testName ++ "\ESC[0m"
  (exitCode, out, err) <- readProcessWithExitCode "runhaskell" ["-i:test", file] ""
  
  -- Always show the output
  when (not $ null out) $ putStr out
  when (not $ null err) $ putStr err
  
  case exitCode of
    ExitSuccess -> return True
    ExitFailure n -> return False
