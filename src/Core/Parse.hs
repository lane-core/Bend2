{-./Type.hs-}

module Core.Parse 
  ( -- * Types
    Parser
  , ParserState(..)
  
  -- * Basic parsers
  , skip
  , lexeme
  , symbol
  , parens
  , angles
  , braces
  , brackets
  , name
  , reserved
  , parseSemi
  
  -- * Character predicates
  , isNameInit
  , isNameChar
  
  -- * Location tracking
  , withSpan
  , located
  
  -- * Error formatting
  , formatError
  ) where

import Control.Monad (when, replicateM, void, guard)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit, isSpace)
import Data.Void
import Debug.Trace
import Highlight (highlightError)
import Text.Megaparsec
import Text.Megaparsec (anySingle, manyTill, lookAhead)
import Text.Megaparsec.Char
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import qualified Text.Megaparsec.Char.Lexer as L

import Core.Bind
import Core.Flatten
import Core.Type

-- Parser state
data ParserState = ParserState
  { tight  :: Bool   -- ^ tracks whether previous token ended with no trailing space
  , noAss  :: Bool   -- ^ when True, disables the parseAss infix operator
  , source :: String -- ^ original file source, for error reporting
  }

type Parser = ParsecT Void String (Control.Monad.State.Strict.State ParserState)

-- | Skip spaces and comments
skip :: Parser ()
skip = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "{-" "-}")

-- Custom lexeme that tracks whether trailing whitespace was consumed.
-- Allows us to distinguish `foo[]` (postfix) from `(foo [])` (application)
lexeme :: Parser a -> Parser a
lexeme p = do
  skip
  x  <- p
  o1 <- getOffset
  skip
  o2 <- getOffset
  st <- get
  put st { tight = o1 == o2 }
  pure x

symbol :: String -> Parser String
symbol s = lexeme (string s)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

isNameInit :: Char -> Bool
isNameInit c = isAsciiLower c || isAsciiUpper c || c == '_'

isNameChar :: Char -> Bool
isNameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_'

name :: Parser Name
name = lexeme $ do
  h <- satisfy isNameInit <?> "letter or underscore"
  t <- many (satisfy isNameChar <?> "letter, digit, or underscore")
  let n = h : t
  if n `elem` reserved
     then fail ("reserved keyword '" ++ n ++ "'")
     else return n

reserved :: [Name]
reserved = ["match","case","else","if","end","all","any","lam"]

-- Parses an Optional semicolon
parseSemi :: Parser ()
parseSemi = optional (symbol ";") >> return ()

-- Location tracking helpers
withSpan :: Parser a -> Parser (Span, a)
withSpan p = do
  -- Record the starting position and absolute offset *before* running the
  -- parser.  The offset is necessary because the location returned by
  -- @getSourcePos@ after the parser has finished may already include trailing
  -- whitespace and comments that @lexeme@ consumed.  We want error spans to
  -- cover only the syntactic construct itself, so we post-process the end
  -- offset to drop such trivia.
  begPos    <- getSourcePos
  begOff    <- getOffset
  x         <- p
  endPosRaw <- getSourcePos  -- position *after* trailing space/comment
  endOffRaw <- getOffset
  st        <- get

  let src = source st

      -- | Skip backwards over whitespace and line comments.  We treat any line
      -- starting with a hash ("# …") as a comment.  The returned offset is the
      -- first position *after* the last non-trivia character (i.e. still
      -- exclusive).
      -- | Compute the new (exclusive) end offset by removing any
      -- trailing
      --   • whitespace (spaces, tabs, new-lines, …)
      --   • whole line comments that start with ‘#’
      --
      -- The algorithm walks backwards from the original end offset until it
      -- finds the last non-trivia character.  For line comments we must drop
      -- the entire line, not just the hash symbol itself.
      trimEnd :: Int -> Int -> Int
      trimEnd b e = step (e - 1)
        where
          -- Walk backwards while we are in whitespace or a comment line.
          step i
            | i < b              = b                    -- fell past start
            | isSpace (src !! i) = step (i - 1)         -- skip whitespace
            | isInCommentLine i  = step (startOfLine i - 1) -- skip comment line
            | otherwise          = i + 1                -- exclusive end

          -- Detect if the character at position @i@ lies within a line whose
          -- first non-space character is ‘#’.  Such a line is considered a
          -- (single-line) comment in Bend.
          isInCommentLine :: Int -> Bool
          isInCommentLine i =
            case firstNonSpace (startOfLine i) of
              Just '#' -> True
              _        -> False
            where
              -- Return the first non-space character between indices @s@ and
              -- the end of the current line (inclusive).  If the line is
              -- empty or contains only spaces it returns @Nothing@.
              firstNonSpace :: Int -> Maybe Char
              firstNonSpace j
                | j >= length src        = Nothing
                | src !! j == '\n'       = Nothing
                | isSpace (src !! j)     = firstNonSpace (j + 1)
                | otherwise              = Just (src !! j)

          -- Find the index of the first character of the current line that
          -- contains index @i@.
          startOfLine :: Int -> Int
          startOfLine j
            | j <= 0           = 0
            | src !! (j - 1) == '\n' = j
            | otherwise        = startOfLine (j - 1)

      trimmedEndOff = trimEnd begOff endOffRaw

      -- Convert absolute index back to a (line, column) pair (both 1-based).
      indexToPos :: String -> Int -> (Int, Int)
      indexToPos s target = go 0 1 1 s
        where
          go idx line col [] = (line, col)
          go idx line col (c:cs)
            | idx == target = (line, col)
            | otherwise =
                let (line', col') = if c == '\n' then (line + 1, 1)
                                     else (line, col + 1)
                in go (idx + 1) line' col' cs

      (begLine, begCol) = (unPos (sourceLine begPos), unPos (sourceColumn begPos))
      (endLine, endCol) = indexToPos src trimmedEndOff

  return (Span (begLine, begCol) (endLine, endCol) src, x)

located :: Parser Term -> Parser Term
located p = do
  (sp, t) <- withSpan p
  return (Loc sp t)

-- | Main entry points
-- These are moved to separate modules to avoid circular dependencies
-- Use Core.Parse.Term for doParseTerm/doReadTerm
-- Use Core.Parse.Book for doParseBook/doReadBook

formatError :: String -> ParseErrorBundle String Void -> String
formatError input bundle = do
  let errorPos = NE.head $ fst $ attachSourcePos errorOffset (bundleErrors bundle) (bundlePosState bundle)
  let err = fst errorPos
  let pos = snd errorPos
  let lin = unPos $ sourceLine pos
  let col = unPos $ sourceColumn pos
  let msg = parseErrorTextPretty err
  let highlighted = highlightError (lin, col) (lin, col+1) input
  "\nPARSE_ERROR\n" ++ msg
    ++ "\nAt line " ++ show lin ++ ", column " ++ show col ++ ":\n"
    ++ highlighted
