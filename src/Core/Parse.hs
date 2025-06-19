{-./Type.hs-}

module Core.Parse where

import Control.Monad (when, replicateM, void, guard)
import Control.Monad.State.Strict (State, get, put)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
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
  beg <- getSourcePos
  x   <- p
  end <- getSourcePos
  let begLine = unPos (sourceLine beg)
  let begCol  = unPos (sourceColumn beg)
  let endLine = unPos (sourceLine end)
  let endCol  = unPos (sourceColumn end)
  st <- get
  return (Span (begLine, begCol) (endLine, endCol) (source st), x)

located :: Parser Term -> Parser Term
located p = do
  (sp, t) <- withSpan p
  return (Loc sp t)

-- | Top‐level entry point
parseTerm :: Parser Term
parseTerm = located $ do
  ini <- parseTermIni
  val <- parseTermEnd ini
  return val

-- | Parse a "core" form (no trailing infix‐style operators)
parseTermIni :: Parser Term
parseTermIni = choice
  [ parseLet
  , parseGen
  , parseTst
  , parseFix
  , parseLam
  , parseUse
  , parseBif
  , parseGet
  , parsePat
  , parseSwi
  , parseMat
  , parseRwt
  , parseAll
  , parseSig
  , parseInd
  , parseSet
  , parseEmp
  , parseEfq
  , parseUni
  , parseOne
  , parseBit
  , parseBt0
  , parseBt1
  , parseNat
  , parseZer
  , parseNatLit
  , parseLstLit
  , parseNil
  , parseRfl
  , parseSuc
  , parseEnu
  , parseSym
  , parseCse
  , parseTupApp
  , parseView
  , parseVar
  ]

-- | After a core form, parse any trailing operators
parseTermEnd :: Term -> Parser Term
parseTermEnd t = do
  t <- parseTermPostfix t
  t <- parseTermInfix t
  return t

-- | Parse chained postfix operators recursively
parseTermPostfix :: Term -> Parser Term
parseTermPostfix t = do
  st <- get
  guard (tight st)
  mb <- optional $ choice
    [ parseCall t
    , parseEql  t
    , parseLst  t ]
  maybe (pure t) parseTermPostfix mb
  <|> pure t

parseTermInfix :: Term -> Parser Term
parseTermInfix t = choice
  [ parseCon t
  , parseFun t
  , parseAnd t
  , parseChk t
  , parseAdd t
  , parseAss t
  , return t ]

parseTupApp :: Parser Term
parseTupApp = do
  _ <- try $ symbol "("
  choice [ parseTup , parseApp ]

-- atomic terms

parseVar :: Parser Term
parseVar = label "variable" $ (\x -> Var x 0) <$> name

parseSet :: Parser Term
parseSet = label "type universe (Set)" $ symbol "Set" >> return Set

parseEmp :: Parser Term
parseEmp = label "empty type (Empty)" $ symbol "Empty" >> return Emp

parseEfq :: Parser Term
parseEfq = label "empty type eliminator (λ{})" $ symbol "λ{}" >> return Efq

parseUni :: Parser Term
parseUni = label "unit type (Unit)" $ symbol "Unit" >> return Uni

parseOne :: Parser Term
parseOne = label "unit value (())" $ symbol "()" >> return One

parseUse :: Parser Term
parseUse = label "unit type eliminator" $ do
  _ <- try $ do
    _ <- symbol "λ{"
    _ <- symbol "()"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  _ <- symbol "}"
  return (Use f)

parseBit :: Parser Term
parseBit = label "bit type (Bool)" $ choice [symbol "Bool", symbol "Bit"] >> return Bit

parseBt0 :: Parser Term
parseBt0 = label "bit zero (False)" $ try $ choice [symbol "False", symbol "False"] >> return Bt0

parseBt1 :: Parser Term
parseBt1 = label "bit one (True)" $ try $ choice [symbol "True", symbol "True"] >> return Bt1

parseBif :: Parser Term
parseBif = choice [ parseBifLambda, parseBifSugar ]

parseBifLambda :: Parser Term
parseBifLambda = label "bit eliminator" $ do
  _ <- try $ do
    _ <- symbol "λ"
    _ <- symbol "{"
    _ <- symbol "False"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  _ <- symbol "True"
  _ <- symbol ":"
  t <- parseTerm
  _ <- parseSemi
  _ <- symbol "}"
  return (Bif f t)

parseBifSugar :: Parser Term
parseBifSugar = parseBifIf

parseBifIf :: Parser Term
parseBifIf = label "if clause" $ do
  _ <- try $ symbol "if"
  condition <- parseTerm
  _ <- symbol ":"
  trueCase <- parseTerm
  _ <- symbol "else"
  _ <- symbol ":"
  falseCase <- parseTerm
  return $ App (Bif falseCase trueCase) condition

parseSwi :: Parser Term
parseSwi = parseSwiLambda

parseSwiLambda :: Parser Term
parseSwiLambda = label "natural number eliminator" $ do
  _ <- try $ do
    _ <- symbol "λ"
    _ <- symbol "{"
    _ <- symbol "0"
    _ <- symbol ":"
    return ()
  z <- parseTerm
  _ <- parseSemi
  _ <- symbol "+"
  _ <- symbol ":"
  s <- parseTerm
  _ <- parseSemi
  _ <- symbol "}"
  return (Swi z s)

parseSig :: Parser Term
parseSig = label "dependent pair type" $ do
  _ <- try $ choice [symbol "Σ", symbol "any"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseSigSimple
    _  -> do
      _ <- symbol "."
      b <- parseTerm
      return $ foldr (\(x, t) acc -> Sig t (Lam x (\v -> acc))) b bindings
  where
    parseBinding = try $ do
      x <- name
      _ <- symbol ":"
      t <- parseTerm
      return (x, t)

parseSigSimple :: Parser Term
parseSigSimple = do
  a <- parseTerm
  _ <- symbol "."
  b <- parseTerm
  return (Sig a b)

parseGet :: Parser Term
parseGet = parseGetLambda

parseGetLambda :: Parser Term
parseGetLambda = label "pair eliminator" $ do
  _ <- try $ do
    _ <- symbol "λ"
    _ <- symbol "{"
    _ <- symbol "(,)"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  _ <- symbol "}"
  return (Get f)

parseAll :: Parser Term
parseAll = label "dependent function type" $ do
  _ <- try $ choice [symbol "∀", symbol "all"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseAllSimple
    _  -> do
      _ <- symbol "."
      b <- parseTerm
      return $ foldr (\(x, t) acc -> All t (Lam x (\v -> acc))) b bindings
  where
    parseBinding = try $ do
      x <- name
      _ <- symbol ":"
      t <- parseTerm
      return (x, t)

parseAllSimple :: Parser Term
parseAllSimple = do
  a <- parseTerm
  _ <- symbol "."
  b <- parseTerm
  return (All a b)


parseMat :: Parser Term
parseMat = parseMatLambda

parseMatLambda :: Parser Term
parseMatLambda = label "list eliminator" $ do
  _ <- try $ do
    _ <- symbol "λ"
    _ <- symbol "{"
    _ <- symbol "[]"
    _ <- symbol ":"
    return ()
  n <- parseTerm
  _ <- parseSemi
  _ <- symbol "<>"
  _ <- symbol ":"
  c <- parseTerm
  _ <- parseSemi
  _ <- symbol "}"
  return (Mat n c)

-- Enum Type Parsers
-- -----------------

parseEnu :: Parser Term
parseEnu = label "enum type" $ do
  _ <- try $ symbol "@{"
  s <- sepBy parseSymbolName (symbol ",")
  _ <- symbol "}"
  return (Enu s)

parseSymbolName :: Parser String
parseSymbolName = do
  _ <- symbol "@"
  n <- some (satisfy isNameChar)
  return n

parseSym :: Parser Term
parseSym = label "enum symbol / constructor" $ try $ do
  _ <- symbol "@"
  notFollowedBy (char '{')          -- make sure we are *not* an Enum "@{"
  n <- some (satisfy isNameChar)
  mfields <- optional $ try $ do
    _ <- symbol "{"
    f <- sepEndBy parseTerm (symbol ",")
    _ <- symbol "}"
    return f
  return $ case mfields of
    Nothing -> Sym n
    Just fs -> buildCtor n fs
  where
    buildCtor :: String -> [Term] -> Term
    buildCtor tag fs =
      let tup = foldl Tup (Sym tag) fs -- (@Tag, f1, f2, …)
      in  Tup tup One                  -- … , ()

parseCse :: Parser Term
parseCse = label "enum case match" $ do
  _ <- try $ do
    _ <- symbol "λ"
    _ <- symbol "{"
    _ <- symbol "@"
    return ()
  f <- some (satisfy isNameChar)
  _ <- symbol ":"
  t <- parseTerm
  r <- many parseCaseClause
  _ <- symbol "}"
  return (Cse ((f, t) : r))

parseCaseClause :: Parser (String, Term)
parseCaseClause = do
  _ <- parseSemi
  _ <- symbol "@"
  s <- some (satisfy isNameChar)
  _ <- symbol ":"
  t <- parseTerm
  return (s, t)

parsePat :: Parser Term
parsePat = label "pattern match" $ do
  srcPos  <- getSourcePos
  _       <- symbol "match"
  scruts  <- some parseTerm
  delim   <- choice [ ':' <$ symbol ":", '{' <$ symbol "{" ]
  moves   <- many parseWith
  clauses <- case delim of
    ':' -> parseIndentClauses (unPos (sourceColumn srcPos)) (length scruts)
    '{' -> parseBraceClauses  (length scruts)
    _   -> fail "unreachable"
  when (delim == '{') (void $ symbol "}")
  _ <- optional (symbol ";")
  pure (Pat scruts moves clauses)
  where
    -- Parse 'with' statements
    parseWith = try $ do
      _ <- symbol "with"
      x <- name
      v <- option (Var x 0) (try (symbol "=" >> parseTerm))
      return (x, v)

-- Indentation-sensitive clause list (stops when out-dented)
parseIndentClauses :: Int -> Int -> Parser [Case]
parseIndentClauses col arity = many1 where
    many1 = do
      first <- clause
      rest  <- many (try clause)
      pure (first:rest)

    clause = label "case clause" . try $ do
      skip                               -- eat leading ws / newlines
      pos  <- getSourcePos
      guard (unPos (sourceColumn pos) >= col)
      _    <- symbol "case"
      pats <- replicateM arity parseTerm
      _    <- symbol ":"
      body <- parseTerm
      pure (pats, body)

-- Braced clause list (runs until the closing '}')
parseBraceClauses :: Int -> Parser [Case]
parseBraceClauses arity = manyTill singleClause (lookAhead (symbol "}")) where
  singleClause = label "case clause" $ do
    _    <- symbol "case"
    pats <- replicateM arity parseTerm
    _    <- symbol ":"
    body <- parseTerm
    pure (pats, body)

parseView :: Parser Term
parseView = label "view" $ do
  try $ do
    _ <- symbol "view"
    _ <- symbol "("
    return ()
  nam <- name
  _ <- symbol ")"
  return $ Var (nam ++ "$") 0

parseNil :: Parser Term
parseNil = label "empty list ([])" $ symbol "[]" >> return Nil

parseNat :: Parser Term
parseNat = label "natural number type (Nat)" $ choice [symbol "Nat", symbol "Nat"] >> return Nat

parseZer :: Parser Term
parseZer = label "zero (0)" $ symbol "0" >> return Zer

parseSuc :: Parser Term
parseSuc = label "successor (↑n)" $ do
  _ <- try $ symbol "↑"
  n <- parseTerm
  return (Suc n)

-- Natural number literal sugar
parseNatLit :: Parser Term
parseNatLit = label "natural number literal" $ lexeme $ do
  (n :: Integer) <- L.decimal
  let build 0 = Zer
      build k = Suc (build (k - 1))
  return (build n)

parseLstLit :: Parser Term
parseLstLit = label "list literal" $ do
  _ <- try $ symbol "["
  terms <- sepEndBy parseTerm (symbol ",")
  _ <- symbol "]"
  return $ foldr Con Nil terms

parseRfl :: Parser Term
parseRfl = label "reflexivity ({==})" $ do
  _ <- try $ do
    _ <- symbol "{"
    _ <- symbol "=="
    return ()
  _ <- symbol "}"
  return Rfl

parseRwt :: Parser Term
parseRwt = parseRwtLambda

parseRwtLambda :: Parser Term
parseRwtLambda = label "rewrite eliminator" $ do
  _ <- try $ do
    _ <- symbol "λ{"
    _ <- symbol "{"
    _ <- symbol "=="
    _ <- symbol "}"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  _ <- symbol "}"
  return (Rwt f)

parseApp :: Parser Term
parseApp = label "application" $ do
  f  <- parseTerm
  xs <- many parseTerm
  _ <- symbol ")"
  return (foldl App f xs)

parseCall :: Term -> Parser Term
parseCall f = label "function application" $ try $ do
  _ <- try $ symbol "("
  args <- sepEndBy parseTerm (symbol ",")
  _ <- symbol ")"
  return $ foldl App f args

observe :: String -> Parser ()
observe traceMsg = do
  remaining <- getInput
  let firstLine = takeWhile (/= '\n') remaining
  trace (traceMsg ++ ":\n    " ++ firstLine) return ()

-- | trailing‐operator parsers
parseTup :: Parser Term
parseTup = label "pair" $ try $ do
  terms <- try $ do
    first <- parseTerm
    _ <- symbol ","
    rest <- sepBy1 parseTerm (symbol ",")
    return (first : rest)
  _ <- symbol ")"
  case terms of
    []     -> fail "empty tuple"
    [x]    -> fail "single element tuple"
    xs     -> return $ foldr1 (\x acc -> Tup x acc) xs

parseTupUnparen :: Term -> Parser Term
parseTupUnparen t = label "unparen pair" $ do
  _ <- try $ symbol ","
  u <- parseTerm
  return (Tup t u)

parseCon :: Term -> Parser Term
parseCon t = label "list cons" $ do
  _ <- try $ symbol "<>"
  u <- parseTerm
  return (Con t u)

parseFun :: Term -> Parser Term
parseFun t = label "function type" $ do
  _ <- try $ symbol "->"
  u <- parseTerm
  return (All t (Lam "_" (\_ -> u)))

parseAnd :: Term -> Parser Term
parseAnd t = label "product type" $ do
  _ <- try $ symbol "&"
  u <- parseTerm
  return (Sig t (Lam "_" (\_ -> u)))

parseChk :: Term -> Parser Term
parseChk x = label "type check" $ do
  _ <- try $ symbol "::"
  t <- parseTerm
  return $ (Chk x t)

parseLst :: Term -> Parser Term
parseLst t = label "list type" $ do
  _ <- try $ symbol "[]"
  return (Lst t)

parseEql :: Term -> Parser Term
parseEql t = label "equality type" $ do
  _ <- try $ symbol "{"
  a <- parseTerm
  _ <- symbol "=="
  b <- parseTerm
  _ <- symbol "}"
  return (Eql t a b)

parseAdd :: Term -> Parser Term
parseAdd t = label "addition" $ do
  _ <- try $ symbol "+"
  b <- parseTerm
  case strip t of
    (Suc Zer) -> return (Suc b)
    _         -> fail "Addition is only supported for (1 + n) which expands to successor"

-- TODO: implement below the 'parseAss' sugar
-- it interprets 'x = v; body' as:
-- - `let x = v; body` (if `x` is a Var)
-- - `match v: case x: body` (otherwise)
parseAss :: Term -> Parser Term
parseAss t = label "location binding" $ do
  st <- get
  if noAss st
    then fail "location binding disabled"
    else do
      _ <- try $ do
        _ <- symbol "="
        notFollowedBy (char '=')
      v <- parseTerm
      _ <- parseSemi
      b <- parseTerm
      case t of
        Var x _ -> return $ Let v (Lam x (\_ -> b))
        _       -> return $ Pat [v] [] [([t], b)]

-- | HOAS‐style binders

parseLam :: Parser Term
parseLam = label "lambda abstraction" $ do
  _ <- try $ do
    _ <- choice [symbol "λ", symbol "lam"]
    notFollowedBy (symbol "{")
    return ()
  xs <- some name
  _  <- symbol "."
  f  <- parseTerm
  return $ foldr (\k acc -> Lam k (\v -> acc)) f xs

parseFix :: Parser Term
parseFix = label "fixed point" $ do
  _ <- try $ symbol "μ"
  k <- name
  _ <- symbol "."
  f <- parseTerm
  return (Fix k (\v -> f))

parseLet :: Parser Term
parseLet = label "let binding" $ do
  _ <- try $ symbol "let"
  x <- name
  choice [ parseLetTyped x , parseLetUntyped x ]

-- Parses the untyped part of a 'let' binding: "= v ; f"
parseLetUntyped :: Name -> Parser Term
parseLetUntyped x = do
  _ <- symbol "="
  v <- parseTerm
  _ <- parseSemi
  f <- parseTerm
  return $ (Let v (Lam x (\_ -> f)))

-- Parses the typed part of a 'let' binding: ": T = v ; f"
parseLetTyped :: Name -> Parser Term
parseLetTyped x = do
  _ <- try $ symbol ":"
  t <- parseTerm
  _ <- symbol "="
  v <- parseTerm
  _ <- parseSemi
  f <- parseTerm
  return $ (Let (Chk v t) (Lam x (\_ -> f)))

parseGen :: Parser Term
parseGen = label "generation" $ do
  _    <- try $ symbol "gen"
  f    <- name
  args <- parens $ sepEndBy parseArg (symbol ",")
  _    <- symbol "->"
  retT <- parseTerm
  ctx  <- option [] parseContext
  body <- parseTerm
  let metT = foldr nestType retT args
  return $ Let (Ann (Met 1 metT ctx) metT) (Lam f (\_ -> body))
  where
    parseArg = (,) <$> name <*> (symbol ":" *> parseTerm)
    nestType (argName, argType) currType = All argType $ Lam argName (\v -> currType)

parseTst :: Parser Term
parseTst = label "test statement" $ do
  _ <- try $ symbol "test"
  a <- parseTerm
  _ <- symbol "=="
  b <- parseTerm
  skip -- FIXME: do NOT use skip outside of 'lexeme'
  _ <- symbol ":"
  t <- parseTerm
  skip
  nxt <- choice [ parseEnd , parseTst ]
  return (Let (Eql t a b) (Lam "_" (\_ -> nxt)))

-- FIXME: what is that for?
parseEnd :: Parser Term
parseEnd = label "end gen statement" $ do
  _ <- try $ symbol "end"
  c <- parseTerm
  return c

parseInd :: Parser Term
parseInd = label "ind" $ choice
  [ parseIndBraced
  , parseIndSimple
  ]

parseIndBraced :: Parser Term
parseIndBraced = do
  _ <- try $ symbol "~{"
  t <- parseTerm
  _ <- symbol "}"
  return (Ind t)

parseIndSimple :: Parser Term
parseIndSimple = do
  _ <- try $ symbol "~"
  t <- parseTerm
  return (Ind t)

parseContext :: Parser [Term]
parseContext = braces $ sepEndBy parseTerm (symbol ",")

-- | Book parsing

parseDefinition :: Parser (Name, Defn)
parseDefinition = choice
  [ parseDataDec
  , parseDefKeyword
  , parseShortDef ]

-- Parse definitions with 'def' keyword
parseDefKeyword :: Parser (Name, Defn)
parseDefKeyword = do
  _ <- symbol "def"
  f <- name
  choice
    [ parseDefFunction f
    , parseDefSimple f ]

-- Parse simple definitions: def name : Type = term
parseDefSimple :: Name -> Parser (Name, Defn)
parseDefSimple defName = do
  _ <- symbol ":"
  typ <- parseTerm
  _ <- symbol "="
  term <- parseTerm
  return (defName, (term, typ))

-- Parse function definitions: def name(args) -> returnType: body
parseDefFunction :: Name -> Parser (Name, Defn)
parseDefFunction f = label "function definition" $ do
  args <- parens $ sepEndBy parseArg (symbol ",")
  _ <- symbol "->"
  returnType <- parseTerm
  _ <- symbol ":"
  body <- parseTerm
  let (typ, bod) = foldr nestTypeBod (returnType, body) args
  return (f, (Fix f (\v -> bod), typ))
  where
    parseArg = (,) <$> name <*> (symbol ":" *> parseTerm)
    nestTypeBod (argName, argType) (currType, currBod) = (All argType (Lam argName (\v -> currType)), Lam argName (\v -> currBod))

-- Parse short definitions: name : Type = term (without 'def' keyword)
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
  return (f, (term, typ))

parseBook :: Parser Book
parseBook = do
  defs <- many parseDefinition
  return $ Book (M.fromList defs)

parseDataDec :: Parser (Name, Defn)
parseDataDec = label "datatype declaration" $ do
  _       <- symbol "data"
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
  return (tName, (term, fullTy))
  where parseArg = (,) <$> name <*> (symbol ":" *> parseTerm)

-- single constructor line
-- Parse a single constructor block inside a datatype declaration.
-- Returns constructor tag together with a list of (fieldName, fieldType)
-- preserving order.
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

doParseTerm :: FilePath -> String -> Either String Term
doParseTerm file input =
  case evalState (runParserT p file input) (ParserState True False input) of
    Left err  -> Left (formatError input err)
    Right res -> Right (bind (flatten res))
  where
    p = do
      skip
      t <- parseTerm
      skip
      eof
      return t

doReadTerm :: String -> Term
doReadTerm input =
  case doParseTerm "<input>" input of
    Left err  -> error err
    Right res -> res

doParseBook :: FilePath -> String -> Either String Book
doParseBook file input =
  case evalState (runParserT p file input) (ParserState True False input) of
    Left err  -> Left (formatError input err)
    Right res -> Right (bindBook (flattenBook res))
  where
    p = do
      skip
      book <- parseBook
      skip
      eof
      return book

doReadBook :: String -> Book
doReadBook input =
  case doParseBook "<input>" input of
    Left err  -> error err
    Right res -> res

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
