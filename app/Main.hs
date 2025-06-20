module Main where

import Control.Monad (unless)
import qualified Data.Map as M
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Core.Cli

-- | Show usage information
showUsage :: IO ()
showUsage = putStrLn "Usage: bend <file.bend>"

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] | ".bend" `isSuffixOf` file -> processFile file
    _ -> showUsage
  where
    isSuffixOf suffix str = reverse suffix == take (length suffix) (reverse str)
