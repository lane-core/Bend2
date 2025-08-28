module Test where

import System.Process
import System.Directory
import System.FilePath
import System.Exit
import Control.Exception (try, throwIO, finally, evaluate)
import Control.Monad (when)
import Data.List (isInfixOf)
import Data.Char (isSpace)
import System.Timeout (timeout)
import System.IO (hClose, hGetContents)

test :: String -> [(String, String)] -> String -> (String -> String -> IO ()) -> IO ()
test cmd files desc callback = testWithTimeout cmd files desc callback (30 * 1000000) -- 30 seconds default

testWithTimeout :: String -> [(String, String)] -> String -> (String -> String -> IO ()) -> Int -> IO ()
testWithTimeout cmd files desc callback timeoutMicros = do
  -- Print description if not empty
  when (not $ null desc) $ putStrLn $ "  " ++ desc
  tmpDir <- getTemporaryDirectory
  testDir <- findUniqueTestDir tmpDir (0 :: Int)
  createDirectory testDir

  -- Capture the test result first
  (out, err) <- finally (runTest testDir) (removeDirectoryRecursive testDir)

  -- Run the callback and check if test passes
  testPassed <- try (callback out err) :: IO (Either ExitCode ())
  let success = case testPassed of
                  Right _ -> True
                  Left _  -> False

  -- Print the bend output (keep ANSI codes for proper formatting)
  let output = out ++ err
  let outputLines = lines output
  let prefix = if success then "  \x1b[32m✓\x1b[0m " else "  \x1b[31m✗\x1b[0m "
  let addPrefix line 
        | null line = ""
        | line `startsWith` "✓ " = "  \x1b[32m" ++ line ++ "\x1b[0m"
        | line `startsWith` "✗ " = "  \x1b[31m" ++ line ++ "\x1b[0m"
        | otherwise = prefix ++ line
      startsWith str prefix = take (length prefix) str == prefix
  mapM_ (putStrLn . addPrefix) outputLines

  -- Re-throw if test failed
  case testPassed of
    Left e  -> throwIO e
    Right _ -> return ()

  where
    findUniqueTestDir base n = do
      let dir = base </> ("bend-test-" ++ show n)
      exists <- doesDirectoryExist dir
      if exists then findUniqueTestDir base (n + 1) else return dir

    -- Corrected runTest function
    runTest testDir = do
      mapM_ (writeTestFile testDir) files

      -- Find project directory by looking for bend.cabal
      projectDir <- findProjectRoot
      
      let cmdWords = words cmd
      let fullCmd = case cmdWords of
                      ("bend":args) -> "cabal run -v0 bend --project-dir=" ++ projectDir ++ " -- " ++ unwords args
                      _             -> cmd

      -- Create the process in its own group to kill it and its children
      let procSpec = (shell $ "cd " ++ testDir ++ " && " ++ fullCmd)
            { std_out = CreatePipe
            , std_err = CreatePipe
            , create_group = True -- IMPORTANT: For POSIX systems (Linux/macOS)
            }

      withCreateProcess procSpec $ \_ mstdout_h mstderr_h ph -> do
        let (Just stdout_h) = mstdout_h
        let (Just stderr_h) = mstderr_h
        -- Use timeout on waiting for the process to complete
        result <- timeout timeoutMicros (waitForProcess ph)

        case result of
          Just _ -> do
            -- Process finished normally, grab output
            out <- hGetContents stdout_h
            err <- hGetContents stderr_h
            -- Fully evaluate the output strings before the handles are closed
            _ <- evaluate (length out + length err)
            return (out, err)
          Nothing -> do
            -- Process timed out. Terminate the entire process group.
            interruptProcessGroupOf ph
            -- Wait for the process to truly die to avoid zombies
            _ <- waitForProcess ph
            return ("", "ERROR: Test timed out after " ++ show (timeoutMicros `div` 1000000) ++ " seconds")

    writeTestFile testDir (name, content) = do
      let path = testDir </> name
      createDirectoryIfMissing True (takeDirectory path)
      writeFile path content

testFile :: String -> String -> (String -> String -> IO ()) -> IO ()
testFile code desc callback = test "bend main.bend" [("main.bend", code)] desc callback

testFileWithTimeout :: String -> String -> (String -> String -> IO ()) -> Int -> IO ()
testFileWithTimeout code desc callback timeoutSeconds = testWithTimeout "bend main.bend" [("main.bend", code)] desc callback (timeoutSeconds * 1000000)

-- Alias for tests that just check if a file type-checks (err == "")
testFileChecks :: String -> IO ()
testFileChecks code = testFile code "must check" $ \out err -> do
  assert (err == "")

-- Test that a file produces a specific goal in the error output
-- Also checks that specific variables have specific types in the context
testFileGoal :: String -> String -> [(String, String)] -> IO ()
testFileGoal code expectedGoal contextChecks =
  testFile code ("must show goal: " ++ expectedGoal) $ \out err -> do
    -- Check that we have a mismatch error (not empty err)
    assert (err /= "")
    -- Check that it's a mismatch error
    assert (err `has` "Mismatch:")
    -- Check that the goal matches
    assert (err `has` ("Goal: " ++ expectedGoal))
    -- Check context variables
    mapM_ (\(varName, varType) -> assert (err `has` ("- " ++ varName ++ " : " ++ varType))) contextChecks

assert :: Bool -> IO ()
assert True  = return ()
assert False = exitFailure

-- Internal helper to strip ANSI colors
stripAnsiColors :: String -> String
stripAnsiColors = stripAnsi
  where
    stripAnsi [] = []
    stripAnsi ('\ESC':'[':xs) = stripAnsi (drop 1 (dropWhile (/= 'm') xs))  -- drop the 'm' too
    stripAnsi (x:xs) = x : stripAnsi xs

-- Find the project root by looking for bend.cabal
findProjectRoot :: IO FilePath
findProjectRoot = do
  cwd <- getCurrentDirectory
  searchUpwards cwd
  where
    searchUpwards :: FilePath -> IO FilePath
    searchUpwards dir = do
      let cabalFile = dir </> "bend.cabal"
      exists <- doesFileExist cabalFile
      if exists
        then return dir
        else do
          let parent = takeDirectory dir
          if parent == dir  -- reached root
            then error "Could not find bend.cabal in any parent directory"
            else searchUpwards parent

-- Infix operator to check if output contains expected text
-- Automatically handles ANSI colors and normalizes whitespace
has :: String -> String -> Bool
output `has` expected =
  let cleanExpected = filter (not . isSpace) expected
      cleanOutput = filter (not . isSpace) (stripAnsiColors output)
  in cleanExpected `isInfixOf` cleanOutput
