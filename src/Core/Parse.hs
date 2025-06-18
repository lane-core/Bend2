{-./Type.hs-}

module Core.Parse where

import Control.Monad.State.Strict (State, get, put)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Void
import Debug.Trace
import Highlight (highlightError)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.List.NonEmpty as NE
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.State.Strict (State, get, put, evalState)

import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Control.Monad (when, replicateM, void)

import Core.Bind
import Core.Flatten
import Core.Type

-- Guideline for future edits
-- --------------------------
-- 1.  Split every rule into:
--       a) a *discriminating prefix* parsed under `try` (so that if the very
--          first token does not match we can still explore other branches);
--       b) the remainder parsed *without* `try` (we are now committed, any
--          failure is a real error, not silent back-tracking).
-- 2.  If several variants share the same prefix (e.g. `Σ (…)` vs `Σ A.`)
--     parse the prefix once, then use `choice` for the mutually exclusive
--     tails—this localises the only back-tracking needed.
-- 3.  Never wrap an entire rule in `try`; doing so degrades error messages
-- 4.  Keep one top-level function per syntactic form; do not inline `do`
--     blocks inside `choice` lists—clarity beats cleverness.
-- 5.  NEVER write a do-block inside a list. Always make a separate function.

-- Parser state with two flags:
-- - tight: tracks whether the previous token ended "tight" (no trailing space).
--          This allows us to distinguish between `foo[]` (list type) and `foo []` (application).
-- - noAss: when True, disables the parseAss infix operator. This is used when parsing
--          types in top-level definitions to prevent `foo : T = x` from parsing the `= x`
--          as part of the type.
data ParserState = ParserState
  { tight :: Bool  -- ^ True if previous token had no trailing whitespace
  , noAss :: Bool  -- ^ True to disable parseAss (for parsing types in definitions)
  }

type Parser = ParsecT Void String (Control.Monad.State.Strict.State ParserState)

-- | Skip spaces and comments (// and /* */)
skip :: Parser ()
skip = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "{-" "-}")

-- Custom lexeme that tracks whether trailing whitespace was consumed.
-- This is necessary to distinguish tight postfix operators (foo[]) from
-- regular function application (foo []).
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
  start <- getSourcePos
  x <- p
  end <- getSourcePos
  return (Span start end, x)

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
  [ 
    parseLet
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
  , parseListLit
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
  if not (tight st)      -- there was a gap → stop
    then pure t
    else do              -- tight → postfixes may follow
      mb <- optional $ choice
              [ parseAppPostfix t
              , parseEql        t
              , parseLst        t
              ]
      maybe (pure t) parseTermPostfix mb

parseTermInfix :: Term -> Parser Term
parseTermInfix t = choice
  [
    parseCon t
  , parseFun t
  , parseAnd t
  , parseChk t
  , parseAdd t
  , parseAss t
  , return t
  ]

parseTupApp :: Parser Term
parseTupApp = do
  _ <- try $ symbol "("
  choice [
      parseTup
    , parseApp
         ]

-- atomic terms

parseVar :: Parser Term
parseVar = label "variable" $ (\x -> Var x 0) <$> name

parseSet :: Parser Term
parseSet = label "type universe (Set)" $ symbol "Set" >> return Set

parseEmp :: Parser Term
parseEmp = label "empty type (⊥)" $ symbol "⊥" >> return Emp

parseEfq :: Parser Term
parseEfq = label "empty type eliminator (λ{})" $ symbol "λ{}" >> return Efq

parseUni :: Parser Term
parseUni = label "unit type (⊤)" $ symbol "⊤" >> return Uni

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
parseBif = choice
  [
    parseBifLambda,
    parseBifSugar
  ]

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
      body <- parseTerm
      return $ foldr (\(x, t) acc -> Sig t (Lam x (\v -> acc))) body bindings
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
      body <- parseTerm
      return $ foldr (\(x, t) acc -> All t (Lam x (\v -> acc))) body bindings
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
parseSym = label "enum symbol" $ do
  _ <- try $ symbol "@"
  n <- some (satisfy isNameChar)
  return (Sym n)

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

-- Constructor tags for coverage checking
data PatClass = PatVar | PatCon ConTag Bool
data ConTag   = ConBt0 | ConBt1 | ConZer | ConSuc | ConNil | ConCon | ConTup | ConOne | ConRfl | ConSym String deriving (Eq, Ord)
data Coverage = CovWild | CovNode (M.Map ConTag Coverage)

-- | Pattern matching with automatic exhaustiveness detection
-- 
-- Consider:
-- Consider:
-- 
--   match x:
--     case True:
--       match y:
--         case 0:
--           ...
--         case 1+p:
--           ...
--     case False:
--       ...
--
-- Since 'match' can have an arbitrary amount of 'cases', then, without
-- significant indentation, there is no way for the parser to decide whether
-- 'case False' belongs on the body of 'match y' or 'match x'. This would
-- require a ';', which, by design, should never be needed.
-- 
-- To solve this issue, we implement a slightly more complex parser, which
-- automatically detects when patterns are exhaustive and stops consuming 'case'
-- clauses. This avoids requiring explicit semicolons.
--
-- Exhaustiveness is determined by tracking which constructors have been seen
-- for each scrutinee position. Once all constructors of a type are covered
-- (or a wildcard is seen), that position is considered complete.
--
-- Additionally, the parser supports 'with' statements that come after the
-- 'match x y ...:' header. These are shaped like 'with x = v' where 'x' is
-- a name and 'v' is a term. They can also be written as just 'with x',
-- which expands to 'with x = x'.
--
-- FIXME: this is AI-generated and probably has flaws. Review it.
parsePat :: Parser Term
parsePat = label "pattern match" $ do
  scruts <- parseMatchHeader
  moves <- parseWithStatements
  clauses <- parseClauses (length scruts) initCov []
  _ <- optional (symbol ";")
  _ <- optional (symbol "}")
  return (Pat scruts moves clauses)
  where
    -- Parse 'match scrut1 scrut2 ... :'
    parseMatchHeader = try $ do
      _ <- symbol "match"
      x <- some parseTerm
      _ <- choice [symbol ":", symbol "{"]
      return x
    
    -- Parse 'with' statements
    parseWithStatements = many parseWith
    
    -- Parse a single 'with x = v' or 'with x'
    parseWith = try $ do
      _ <- symbol "with"
      x <- name
      v <- option (Var x 0) (try (symbol "=" >> parseTerm))
      return (x, v)
    
    -- Parse a single 'case pat1 pat2 ... : body'
    parseClause arity = do
      _ <- symbol "case"
      pats <- replicateM arity parseTerm
      _ <- symbol ":"
      body <- parseTerm
      return (pats, body)
    
    -- Parse clauses until exhaustive or no more 'case' keywords
    parseClauses arity cov acc = do
      hasCase <- isNextCase
      if not hasCase || isExhaustive cov
        then return (reverse acc)
        else do
          clause@(pats, _) <- parseClause arity
          let cov' = addPatterns pats cov
          parseClauses arity cov' (clause : acc)
    
    -- Check if next token is 'case'
    isNextCase = option False (True <$ lookAhead (symbol "case"))
    
    -- Coverage tracking
    initCov = CovNode M.empty
    
    -- Add pattern vector to coverage tree
    addPatterns [] cov = cov
    addPatterns _ CovWild = CovWild
    addPatterns (p:ps) (CovNode m) = 
      case classifyPattern p of
        PatVar -> CovWild  -- variable covers everything
        PatCon c generic ->
          let subtree = M.findWithDefault initCov c m
              subtree' = if null ps && generic
                           then CovWild  -- generic constructor
                           else addPatterns ps subtree
          in CovNode (M.insert c subtree' m)
    
    -- Classify a pattern
    classifyPattern p = case p of
      Var _ _ -> PatVar
      Bt0     -> PatCon ConBt0 True
      Bt1     -> PatCon ConBt1 True
      Zer     -> PatCon ConZer True
      Suc x   -> PatCon ConSuc (isVar x)
      Nil     -> PatCon ConNil True
      Con x y -> PatCon ConCon (isVar x && isVar y)
      Tup x y -> PatCon ConTup (isVar x && isVar y)
      One     -> PatCon ConOne True
      Rfl     -> PatCon ConRfl True
      Sym s   -> PatCon (ConSym s) True
      Loc _ t -> classifyPattern t
      _       -> PatVar  -- treat other patterns as wildcards
    
    -- Check if term is a variable
    isVar t = case t of
      Var _ _ -> True
      Loc _ t -> isVar t
      _       -> False
    
    -- Check if coverage is exhaustive
    isExhaustive CovWild = True
    isExhaustive (CovNode m)
      | M.null m = False
      | otherwise = 
          let have = M.keysSet m
              need = requiredCons (head $ M.keys m)
          in have == need && all isExhaustive (M.elems m)
    
    -- Get required constructors for a constructor family
    requiredCons c = case c of
      ConBt0 -> S.fromList [ConBt0, ConBt1]
      ConBt1 -> S.fromList [ConBt0, ConBt1]
      ConZer -> S.fromList [ConZer, ConSuc]
      ConSuc -> S.fromList [ConZer, ConSuc]
      ConNil -> S.fromList [ConNil, ConCon]
      ConCon -> S.fromList [ConNil, ConCon]
      ConSym _ -> S.empty  -- Enum symbols never exhaustive alone
      _ -> S.singleton c

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

parseListLit :: Parser Term
parseListLit = label "list literal" $ do
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

parseAppPostfix :: Term -> Parser Term
parseAppPostfix f = label "function application" $ try $ do
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
      v    <- parseTerm
      _    <- parseSemi
      body <- parseTerm
      case t of
        Var x _ -> return $ Let v (Lam x (\_ -> body))
        _       -> return $ Pat [v] [] [([t], body)]

-- | HOAS‐style binders

parseLam :: Parser Term
parseLam = label "lambda abstraction" $ do
  _ <- try $ do
    _ <- choice [symbol "λ", symbol "lam"]
    notFollowedBy (symbol "{")
    return ()
  names <- some name
  _ <- symbol "."
  body <- parseTerm
  return $ foldr (\k acc -> Lam k (\v -> acc)) body names

parseFix :: Parser Term
parseFix = label "fixed point" $ do
  _ <- try $ symbol "μ"
  k <- name
  _ <- symbol "."
  body <- parseTerm
  return (Fix k (\v -> body))

parseLet :: Parser Term
parseLet = label "let binding" $ choice
  [ parseLetBang
  , parseLetKeyword
  ]

parseLetBang :: Parser Term
parseLetBang = do
  _ <- try $ symbol "!"
  v <- parseTerm
  _ <- parseSemi
  f <- parseTerm
  return (Let v f)

parseLetKeyword :: Parser Term
parseLetKeyword = do
  _ <- try $ symbol "let"
  x <- name
  choice
    [ parseLetTyped x
    , parseLetUntyped x
    ]

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
  _ <- try $ symbol "tst"
  a <- parseTerm
  _ <- symbol "=="
  b <- parseTerm
  skip -- FIXME: do NOT use skip outside of 'lexeme'
  _ <- symbol ":"
  t <- parseTerm
  skip
  nxt <- choice [ parseEnd , parseTst ]
  return (Let (Eql t a b) (Lam "_" (\_ -> nxt)))

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
  [ parseDefKeyword
  , parseShortDef
  ]

-- Parse definitions with 'def' keyword
parseDefKeyword :: Parser (Name, Defn)
parseDefKeyword = do
  _ <- symbol "def"
  f <- name
  choice
    [ parseDefFunction f
    , parseDefSimple f
    ]

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

-- | Main entry points

doParseTerm :: FilePath -> String -> Either String Term
doParseTerm file input =
  case evalState (runParserT p file input) (ParserState True False) of
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
  case evalState (runParserT p file input) (ParserState True False) of
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
