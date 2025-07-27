module Test where

import System.Process
import System.Directory
import System.FilePath
import System.Exit
import Control.Exception (try, throwIO, finally)
import Control.Monad (when)
import Data.List (isInfixOf)
import Data.Char (isSpace)

test :: String -> [(String, String)] -> String -> (String -> String -> IO ()) -> IO ()
test cmd files desc callback = do
  -- Print description if not empty
  when (not $ null desc) $ putStrLn $ "  \ESC[2m" ++ desc ++ "\ESC[0m"  -- dim/gray
  tmpDir <- getTemporaryDirectory
  testDir <- findUniqueTestDir tmpDir (0 :: Int)
  createDirectory testDir
  
  -- Capture the test result first
  (out, err) <- finally (runTest testDir) (removeDirectoryRecursive testDir)
  
  -- Run the callback and check if test passes
  testPassed <- try (callback out err) :: IO (Either ExitCode ())
  let success = case testPassed of
                  Right _ -> True
                  Left _ -> False
  
  -- Print the bend output with appropriate color
  let output = out ++ err
  let outputLines = lines output
  let color = if success then "\ESC[32m" else "\ESC[31m"
  let resetColor = "\ESC[0m"
  mapM_ (\line -> putStrLn $ "  " ++ color ++ ">" ++ resetColor ++ " " ++ line) outputLines
  
  -- Re-throw if test failed
  case testPassed of
    Left e -> throwIO e
    Right _ -> return ()
  
  where
    findUniqueTestDir base n = do
      let dir = base </> ("bend-test-" ++ show n)
      exists <- doesDirectoryExist dir
      if exists then findUniqueTestDir base (n + 1) else return dir
    
    runTest testDir = do
      mapM_ (writeTestFile testDir) files
      
      let cmdWords = words cmd
      let projectDir = "/Users/v/vic/dev/bend2"
      let fullCmd = case cmdWords of
                      ("bend":args) -> "cabal run -v0 bend --project-dir=" ++ projectDir ++ " -- " ++ unwords args
                      _             -> cmd
      
      (exitCode, out, err) <- readProcessWithExitCode "sh" ["-c", "cd " ++ testDir ++ " && " ++ fullCmd] ""
      
      return (out, err)
    
    writeTestFile testDir (name, content) = do
      let path = testDir </> name
      createDirectoryIfMissing True (takeDirectory path)
      writeFile path content

testFile :: String -> String -> (String -> String -> IO ()) -> IO ()
testFile code desc callback = test "bend main.bend" [("main.bend", code)] desc callback

-- Alias for tests that just check if a file type-checks (err == "")
testFileChecks :: String -> IO ()
testFileChecks code = testFile code "must check" $ \out err -> do
  assert (err == "")

assert :: Bool -> IO ()
assert True = return ()
assert False = exitFailure

-- Internal helper to strip ANSI colors
stripAnsiColors :: String -> String
stripAnsiColors = stripAnsi
  where
    stripAnsi [] = []
    stripAnsi ('\ESC':'[':xs) = stripAnsi (dropWhile (/= 'm') xs)
    stripAnsi (x:xs) = x : stripAnsi xs

-- Infix operator to check if output contains expected text
-- Automatically handles ANSI colors and normalizes whitespace
has :: String -> String -> Bool
output `has` expected =
  let cleanExpected = filter (not . isSpace) expected
      cleanOutput = filter (not . isSpace) (stripAnsiColors output)
  in cleanExpected `isInfixOf` cleanOutput

