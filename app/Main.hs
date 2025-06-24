module Main where

import Control.Monad (unless)
import qualified Data.Map as M
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Core.CLI (processFile, processFileToJS, listDependencies)

-- | Show usage information
showUsage :: IO ()
showUsage = do
  putStrLn "Usage: bend <file.bend> [options]"
  putStrLn ""
  putStrLn "Options:"
  putStrLn "  --to-javascript    Compile to JavaScript"
  putStrLn "  --list-dependencies List all dependencies (recursive)"

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    [file, "--to-javascript"] | ".bend"    `isSuffixOf` file -> processFileToJS file
    [file, "--to-javascript"] | ".bend.py" `isSuffixOf` file -> processFileToJS file
    [file, "--list-dependencies"] | ".bend"    `isSuffixOf` file -> listDependencies file
    [file, "--list-dependencies"] | ".bend.py" `isSuffixOf` file -> listDependencies file
    [file] | ".bend"    `isSuffixOf` file -> processFile file
    [file] | ".bend.py" `isSuffixOf` file -> processFile file
    otherwise                             -> showUsage
  where isSuffixOf suffix str = reverse suffix == take (length suffix) (reverse str)
