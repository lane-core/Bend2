{-./Type.hs-}

module Core.Parse.Term 
  ( parseTerm
  , doParseTerm
  , doReadTerm
  ) where

import Control.Monad (when, replicateM, void, guard)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Void
import Debug.Trace
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
import Core.Parse (Parser, ParserState(..), skip, lexeme, symbol, parens, angles, 
                  braces, brackets, name, reserved, parseSemi, isNameInit, 
                  isNameChar, withSpan, located, formatError)

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

-- | Helper: parses infix operators (->  &  ::  +  =)
parseTermInfix :: Term -> Parser Term
parseTermInfix t = choice
  [ parseCon t
  , parseFun t
  , parseAnd t
  , parseChk t
  , parseAdd t
  , parseAss t
  , return t ]

-- | Syntax: (term1, term2) | (f arg1 arg2)
-- Disambiguates between tuples and applications
parseTupApp :: Parser Term
parseTupApp = do
  _ <- try $ symbol "("
  choice [ parseTup , parseApp ]

-- atomic terms

-- | Syntax: x, foo, bar_123
parseVar :: Parser Term
parseVar = label "variable" $ (\x -> Var x 0) <$> name

-- | Syntax: Set
parseSet :: Parser Term
parseSet = label "type universe (Set)" $ symbol "Set" >> return Set

-- | Syntax: Empty
parseEmp :: Parser Term
parseEmp = label "empty type (Empty)" $ symbol "Empty" >> return Emp

-- | Syntax: λ{}
parseEfq :: Parser Term
parseEfq = label "empty type eliminator (λ{})" $ symbol "λ{}" >> return Efq

-- | Syntax: Unit
parseUni :: Parser Term
parseUni = label "unit type (Unit)" $ symbol "Unit" >> return Uni

-- | Syntax: ()
parseOne :: Parser Term
parseOne = label "unit value (())" $ symbol "()" >> return One

-- | Syntax: λ{ (): term; }
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

-- | Syntax: Bool | Bit
parseBit :: Parser Term
parseBit = label "bit type (Bool)" $ choice [symbol "Bool", symbol "Bit"] >> return Bit

-- | Syntax: False
parseBt0 :: Parser Term
parseBt0 = label "bit zero (False)" $ try $ choice [symbol "False", symbol "False"] >> return Bt0

-- | Syntax: True
parseBt1 :: Parser Term
parseBt1 = label "bit one (True)" $ try $ choice [symbol "True", symbol "True"] >> return Bt1

-- | Syntax: λ{ False: term; True: term; } | if cond: term else: term
parseBif :: Parser Term
parseBif = choice [ parseBifLambda, parseBifSugar ]

-- | Syntax: λ{ False: term; True: term; }
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

-- | Helper: sugar syntax for bit elimination
parseBifSugar :: Parser Term
parseBifSugar = parseBifIf

-- | Syntax: if condition: trueCase else: falseCase
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

-- | Syntax: λ{ 0: zeroCase; +: successorCase; }
parseSwi :: Parser Term
parseSwi = parseSwiLambda

-- | Syntax: λ{ 0: zeroCase; +: successorCase; }
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

-- | Syntax: Σ x: Type. body | any x: Type. body | Σ Type. Type | any Type. Type
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

-- | Syntax: Type . Type
-- Simplified form of dependent pair without binding
parseSigSimple :: Parser Term
parseSigSimple = do
  a <- parseTerm
  _ <- symbol "."
  b <- parseTerm
  return (Sig a b)

-- | Syntax: λ{ (,): eliminator; }
parseGet :: Parser Term
parseGet = parseGetLambda

-- | Syntax: λ{ (,): eliminator; }
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

-- | Syntax: ∀ x: Type. body | all x: Type. body | ∀ Type. Type | all Type. Type
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

-- | Syntax: Type . Type
-- Simplified form of dependent function without binding
parseAllSimple :: Parser Term
parseAllSimple = do
  a <- parseTerm
  _ <- symbol "."
  b <- parseTerm
  return (All a b)

-- | Syntax: λ{ []: nilCase; <>: consCase; }
parseMat :: Parser Term
parseMat = parseMatLambda

-- | Syntax: λ{ []: nilCase; <>: consCase; }
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

-- | Syntax: @{tag1, tag2, tag3}
parseEnu :: Parser Term
parseEnu = label "enum type" $ do
  _ <- try $ symbol "@{"
  s <- sepBy parseSymbolName (symbol ",")
  _ <- symbol "}"
  return (Enu s)

-- | Syntax: @name
-- Helper for parsing enum tag names
parseSymbolName :: Parser String
parseSymbolName = do
  _ <- symbol "@"
  n <- some (satisfy isNameChar)
  return n

-- | Syntax: @tag | @tag{field1, field2}
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
      let tup = foldr Tup One fs       -- Build (f1,(f2,(...,()))
      in  Tup (Sym tag) tup            -- (@Tag,(f1,(f2,(...,()))))

-- | Syntax: λ{ @tag1: term1; @tag2: term2; }
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

-- | Syntax: @tag: term
-- Helper for parsing enum case clauses
parseCaseClause :: Parser (String, Term)
parseCaseClause = do
  _ <- parseSemi
  _ <- symbol "@"
  s <- some (satisfy isNameChar)
  _ <- symbol ":"
  t <- parseTerm
  return (s, t)

-- | Syntax: match expr: case pat: body | match expr { case pat: body }
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

-- | Syntax: case pattern1 pattern2: body
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

-- | Syntax: case pattern1 pattern2: body
-- Braced clause list (runs until the closing '}')
parseBraceClauses :: Int -> Parser [Case]
parseBraceClauses arity = manyTill singleClause (lookAhead (symbol "}")) where
  singleClause = label "case clause" $ do
    _    <- symbol "case"
    pats <- replicateM arity parseTerm
    _    <- symbol ":"
    body <- parseTerm
    pure (pats, body)

-- | Syntax: view(functionName)
parseView :: Parser Term
parseView = label "view" $ do
  try $ do
    _ <- symbol "view"
    _ <- symbol "("
    return ()
  nam <- name
  _ <- symbol ")"
  return $ Var (nam ++ "$") 0

-- | Syntax: []
parseNil :: Parser Term
parseNil = label "empty list ([])" $ symbol "[]" >> return Nil

-- | Syntax: Nat
parseNat :: Parser Term
parseNat = label "natural number type (Nat)" $ choice [symbol "Nat", symbol "Nat"] >> return Nat

-- | Syntax: 0
parseZer :: Parser Term
parseZer = label "zero (0)" $ symbol "0" >> return Zer

-- | Syntax: ↑term
parseSuc :: Parser Term
parseSuc = label "successor (↑n)" $ do
  _ <- try $ symbol "↑"
  n <- parseTerm
  return (Suc n)

-- | Syntax: 1, 2, 3, 42, 123
parseNatLit :: Parser Term
parseNatLit = label "natural number literal" $ lexeme $ do
  (n :: Integer) <- L.decimal
  let build 0 = Zer
      build k = Suc (build (k - 1))
  return (build n)

-- | Syntax: [term1, term2, term3]
parseLstLit :: Parser Term
parseLstLit = label "list literal" $ do
  _ <- try $ symbol "["
  terms <- sepEndBy parseTerm (symbol ",")
  _ <- symbol "]"
  return $ foldr Con Nil terms

-- | Syntax: {==}
parseRfl :: Parser Term
parseRfl = label "reflexivity ({==})" $ do
  _ <- try $ do
    _ <- symbol "{"
    _ <- symbol "=="
    return ()
  _ <- symbol "}"
  return Rfl

-- | Syntax: λ{ {==}: term; }
parseRwt :: Parser Term
parseRwt = parseRwtLambda

-- | Syntax: λ{ {==}: term; }
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

-- | Syntax: (function arg1 arg2 arg3)
parseApp :: Parser Term
parseApp = label "application" $ do
  f  <- parseTerm
  xs <- many parseTerm
  _ <- symbol ")"
  return (foldl App f xs)

-- | Syntax: function(arg1, arg2, arg3) | function<A, B>(arg1, arg2)
parseCall :: Term -> Parser Term
parseCall f = label "function application" $ try $ do
  -- Parse optional type arguments <A, B, ...>
  typeArgs <- option [] $ try $ angles $ sepEndBy parseTerm (symbol ",")
  _ <- symbol "("
  args <- sepEndBy parseTerm (symbol ",")
  _ <- symbol ")"
  -- Combine type args with regular args
  let allArgs = typeArgs ++ args
  return $ foldl App f allArgs

-- | Helper: debugging function to trace parser state
observe :: String -> Parser ()
observe traceMsg = do
  remaining <- getInput
  let firstLine = takeWhile (/= '\n') remaining
  trace (traceMsg ++ ":\n    " ++ firstLine) return ()

-- | trailing‐operator parsers

-- | Syntax: (term1, term2) | (term1, term2, term3)
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

-- | Syntax: term1, term2
parseTupUnparen :: Term -> Parser Term
parseTupUnparen t = label "unparen pair" $ do
  _ <- try $ symbol ","
  u <- parseTerm
  return (Tup t u)

-- | Syntax: head <> tail
parseCon :: Term -> Parser Term
parseCon t = label "list cons" $ do
  _ <- try $ symbol "<>"
  u <- parseTerm
  return (Con t u)

-- | Syntax: InputType -> OutputType
parseFun :: Term -> Parser Term
parseFun t = label "function type" $ do
  _ <- try $ symbol "->"
  u <- parseTerm
  return (All t (Lam "_" (\_ -> u)))

-- | Syntax: Type1 & Type2
parseAnd :: Term -> Parser Term
parseAnd t = label "product type" $ do
  _ <- try $ symbol "&"
  u <- parseTerm
  return (Sig t (Lam "_" (\_ -> u)))

-- | Syntax: term :: Type
parseChk :: Term -> Parser Term
parseChk x = label "type check" $ do
  _ <- try $ symbol "::"
  t <- parseTerm
  return $ (Chk x t)

-- | Syntax: ElementType[]
parseLst :: Term -> Parser Term
parseLst t = label "list type" $ do
  _ <- try $ symbol "[]"
  return (Lst t)

-- | Syntax: Type{term1 == term2}
parseEql :: Term -> Parser Term
parseEql t = label "equality type" $ do
  _ <- try $ symbol "{"
  a <- parseTerm
  _ <- symbol "=="
  b <- parseTerm
  _ <- symbol "}"
  return (Eql t a b)

-- | Syntax: 1 + n
parseAdd :: Term -> Parser Term
parseAdd t = label "addition" $ do
  _ <- try $ symbol "+"
  b <- parseTerm
  case strip t of
    (Suc Zer) -> return (Suc b)
    _         -> fail "Addition is only supported for (1 + n) which expands to successor"

-- | Syntax: var = value; body | pattern = value; body
-- Interprets as let if t is a variable, otherwise as pattern match
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

-- | Syntax: λ x y z. body | lam x y z. body
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

-- | Syntax: μ f. body
parseFix :: Parser Term
parseFix = label "fixed point" $ do
  _ <- try $ symbol "μ"
  k <- name
  _ <- symbol "."
  f <- parseTerm
  return (Fix k (\v -> f))

-- | Syntax: let x = value; body | let x : Type = value; body
parseLet :: Parser Term
parseLet = label "let binding" $ do
  _ <- try $ symbol "let"
  x <- name
  choice [ parseLetTyped x , parseLetUntyped x ]

-- | Syntax: = value; body
-- Parses the untyped part of a 'let' binding
parseLetUntyped :: Name -> Parser Term
parseLetUntyped x = do
  _ <- symbol "="
  v <- parseTerm
  _ <- parseSemi
  f <- parseTerm
  return $ (Let v (Lam x (\_ -> f)))

-- | Syntax: : Type = value; body
-- Parses the typed part of a 'let' binding
parseLetTyped :: Name -> Parser Term
parseLetTyped x = do
  _ <- try $ symbol ":"
  t <- parseTerm
  _ <- symbol "="
  v <- parseTerm
  _ <- parseSemi
  f <- parseTerm
  return $ (Let (Chk v t) (Lam x (\_ -> f)))

-- | Syntax: gen name(x: Type1, y: Type2) -> RetType { context } body
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

-- | Syntax: test term1 == term2 : Type ...
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

-- | Syntax: end term
parseEnd :: Parser Term
parseEnd = label "end gen statement" $ do
  _ <- try $ symbol "end"
  c <- parseTerm
  return c

-- | Syntax: ~{term} | ~term
parseInd :: Parser Term
parseInd = label "ind" $ choice
  [ parseIndBraced
  , parseIndSimple
  ]

-- | Syntax: ~{term}
parseIndBraced :: Parser Term
parseIndBraced = do
  _ <- try $ symbol "~{"
  t <- parseTerm
  _ <- symbol "}"
  return (Ind t)

-- | Syntax: ~term
parseIndSimple :: Parser Term
parseIndSimple = do
  _ <- try $ symbol "~"
  t <- parseTerm
  return (Ind t)

-- | Syntax: {term1, term2, term3}
-- Helper for parsing context in gen statements
parseContext :: Parser [Term]
parseContext = braces $ sepEndBy parseTerm (symbol ",")

-- | Main entry points

-- | Parse a term from a string, returning an error message on failure
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

-- | Parse a term from a string, crashing on failure
doReadTerm :: String -> Term
doReadTerm input =
  case doParseTerm "<input>" input of
    Left err  -> error err
    Right res -> res
