{-./Type.hs-}

module Core.Parse.Book 
  ( parseBook
  , doParseBook
  , doReadBook
  ) where

import Control.Monad (when)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Map.Strict as M
import qualified Text.Megaparsec.Char.Lexer as L

import Core.Type
import Core.Move
import Core.Parse (Parser, ParserState(..), skip, lexeme, symbol, parens, angles, 
                  braces, brackets, name, reserved, parseSemi, isNameInit, 
                  isNameChar, withSpan, located, formatError)
import Core.Parse.Term (parseTerm)
import Core.Bind (bindBook)
import Core.Flatten (flattenBook)

-- | Book parsing

-- | Syntax: def name : Type = term | type Name<T>(i) -> Type: cases | name : Type = term
parseDefinition :: Parser (Name, Defn)
parseDefinition = choice
  [ parseDataDec
  , parseDefKeyword
  , parseShortDef ]

-- | Syntax: def name : Type = term | def name(x: T1, y: T2) -> RetType: body
parseDefKeyword :: Parser (Name, Defn)
parseDefKeyword = do
  _ <- symbol "def"
  f <- name
  choice
    [ parseDefFunction f
    , parseDefSimple f ]

-- | Syntax: def name : Type = term
parseDefSimple :: Name -> Parser (Name, Defn)
parseDefSimple defName = do
  _ <- symbol ":"
  typ <- parseTerm
  _ <- symbol "="
  term <- parseTerm
  return (defName, (False, term, typ))

-- | Syntax: def name(x: Type1, y: Type2) -> ReturnType: body
--           def name<A, B>(x: Type1, y: Type2) -> ReturnType: body
parseDefFunction :: Name -> Parser (Name, Defn)
parseDefFunction f = label "function definition" $ do
  -- Parse optional generic type parameters <A, B, ...>
  typeParams <- option [] $ angles $ sepEndBy name (symbol ",")
  -- Convert type params to arguments with type Set
  let typeArgs = [(tp, Set) | tp <- typeParams]
  -- Parse regular arguments
  regularArgs <- parens $ sepEndBy parseArg (symbol ",")
  -- Combine type params (as Set-typed args) with regular args
  let args = typeArgs ++ regularArgs
  _ <- symbol "->"
  returnType <- parseTerm
  _ <- symbol ":"
  body <- parseTerm
  let (typ, bod) = foldr nestTypeBod (returnType, body) args
  return (f, (False, Fix f (\v -> bod), typ))
  where
    parseArg = (,) <$> name <*> (symbol ":" *> parseTerm)
    nestTypeBod (argName, argType) (currType, currBod) = (All argType (Lam argName (\v -> currType)), Lam argName (\v -> currBod))

-- | Syntax: name : Type = term (without 'def' keyword)
parseShortDef :: Parser (Name, Defn)
parseShortDef = label "short definition" $ try $ do
  f <- name
  _ <- symbol ":"
  -- Temporarily disable parseAss while parsing the type
  st <- get
  put st { noAss = True }
  typ <- parseTerm
  put st { noAss = False }
  _ <- symbol "="
  term <- parseTerm
  return (f, (False, term, typ))

-- | Syntax: def1 def2 def3 ...
parseBook :: Parser Book
parseBook = do
  defs <- many parseDefinition
  return $ Book (M.fromList defs)

-- | Syntax: type Name<T, U>(i: Nat) -> Type: case @Tag1: field1: T1 case @Tag2: field2: T2
parseDataDec :: Parser (Name, Defn)
parseDataDec = label "datatype declaration" $ do
  _       <- symbol "type"
  tName   <- name
  params  <- option [] $ angles (sepEndBy parseArg (symbol ","))
  indices <- option [] $ parens (sepEndBy parseArg (symbol ","))
  args    <- return $ params ++ indices
  retTy   <- option Set (symbol "->" *> parseTerm)
  _       <- symbol ":"
  cases   <- many parseDataCase
  when (null cases) $ fail "datatype must have at least one constructor case"
  let tags = map fst cases
      mkFields :: [(Name, Term)] -> Term
      mkFields []             = Uni
      mkFields ((fn,ft):rest) = Sig ft (Lam fn (\_ -> mkFields rest))
      --   match ctr: case @Tag: …
      branches v = Pat [v] [] [([Sym tag], mkFields flds) | (tag, flds) <- cases]
      -- The body of the definition (see docstring).
      body0 = Sig (Enu tags) (Lam "ctr" (\v -> branches v))
      -- Wrap the body with lambdas for the parameters.
      nest (n, ty) (tyAcc, bdAcc) = (All ty  (Lam n (\_ -> tyAcc)) , Lam n (\_ -> bdAcc))
      (fullTy, fullBody) = foldr nest (retTy, body0) args
      term = Fix tName (\_ -> fullBody)
  return (tName, (True, term, fullTy))
  where parseArg = (,) <$> name <*> (symbol ":" *> parseTerm)

-- | Syntax: case @Tag: field1: Type1 field2: Type2
parseDataCase :: Parser (String, [(Name, Term)])
parseDataCase = label "datatype constructor" $ do
  _    <- symbol "case"
  _    <- symbol "@"
  tag  <- some (satisfy isNameChar)
  _    <- symbol ":"
  flds <- many parseField
  return (tag, flds)
  where
    -- Parse a field declaration  name : Type
    parseField :: Parser (Name, Term)
    parseField = try $ do
      -- Stop if next token is 'case' (start of next constructor) or 'def'/'data'
      notFollowedBy (symbol "case")
      n <- name
      _ <- symbol ":"
      t <- parseTerm
      -- Optional semicolon or newline is already handled by lexeme
      return (n,t)

-- | Main entry points

-- | Parse a book from a string, returning an error message on failure
doParseBook :: FilePath -> String -> Either String Book
doParseBook file input =
  case evalState (runParserT p file input) (ParserState True False input) of
    Left err  -> Left (formatError input err)
    Right res -> Right (bindBook (moveBook (flattenBook res)))
  where
    p = do
      skip
      book <- parseBook
      skip
      eof
      return book

-- | Parse a book from a string, crashing on failure
doReadBook :: String -> Book
doReadBook input =
  case doParseBook "<input>" input of
    Left err  -> error err
    Right res -> res
    Right res -> res
