{-./../Type.hs-}
{-./../Parse.hs-}
{-# LANGUAGE ViewPatterns #-}

module Core.Parse.Term (
  parseExpr,
  parseExprBefore,
  doParseExpr,
  doReadExpr,
) where

import Control.Monad (guard, replicateM, void, when)
import Control.Monad.State.Strict (State, evalState, get, put)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Void
import Data.Word (Word64)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

import Debug.Trace

import Core.Adjust.Adjust
import Core.Parse.Parse
-- import Core.Legacy.Show -- Merged into Sort.hs
import Core.Sort

-- | Parse a "core" form
parseExprIni :: Parser Expr
parseExprIni =
  choice
    [ parseFix
    , parseLam
    , parseLamMatch
    , parseBifIf
    , parsePat
    , parseRewrite
    , parseAbsurd
    , parseFrk
    , parseTrust
    , parseLog
    , parseAll
    , parseSig
    , parseTildeExpr
    , parseOne
    , parseEra
    , parseSup
    , parseReturn
    , parseNat
    , parseNatLit
    , parseNumLit
    , parseNumUna
    , parseCharLit
    , parseStringLit
    , parseLstLit
    , parseNil
    , parseRfl
    , parseEnu
    , parseSym
    , parseTupApp
    , parseView
    , parseVar
    ]

-- | Parse a "tight" postfix: f(...) | f[] | f{x == y} ...
parseExprArg :: Expr -> Parser Expr
parseExprArg t =
  do
    st <- get
    guard (tight st)
    mb <-
      optional $
        choice
          [ parsePol t -- f<...>
          , parseCal t -- f(...)
          , parseEql t -- f{x == y}
          , parseLst t -- f[]
          ]
    maybe (pure t) parseExprArg mb
    <|> pure t

-- | Parse a "loose" postfix: f + x | f <> x | ...
parseExprOpr :: Expr -> Parser Expr
parseExprOpr t =
  choice
    [ parseCon t -- <>
    , parseFun t -- ->
    , parseAnd t -- &
    , parseChk t -- ::
    , parseAdd t -- +
    , parseNumOp t -- <, >, ==, etc.
    , parseAss t -- =
    , return t
    ]

{- | A helper that conditionally applies a postfix/infix parser to a term.
The parser is only applied if the next token is not in the 'blocked' list.
This is the core of the operator-blocking mechanism that allows for context-
sensitive parsing, preventing ambiguity in expressions like `~ term { ... }`.
| A helper that conditionally applies a postfix/infix parser to a term.
The parser is only applied if the next token is not in the 'blocked' list.
This is the core of the operator-blocking mechanism that allows for context-
sensitive parsing, preventing ambiguity in expressions like `if ...:` or
`~ term { ... }`, where certain trailing operators must not be parsed.
-}
withOperatorParsing :: Expr -> (Expr -> Parser Expr) -> Parser Expr
withOperatorParsing term operatorParser = do
  st <- get
  -- If the blocked list is empty, we can always parse the operator.
  if null (blocked st)
    then operatorParser term
    else do
      -- Peek ahead to see if the next token is a blocked operator.
      -- `lookAhead` does this without consuming input. `symbol` handles whitespace.
      isBlocked <- optional . lookAhead . choice . map (try . symbol) $ blocked st
      case isBlocked of
        -- The next token is blocked, so we must not parse it as an operator.
        -- We return the term as-is, without applying the operator parser.
        Just _ -> return term
        -- The next token is not blocked, so we proceed with the operator parser.
        Nothing -> operatorParser term

{- | Top-level entry point for parsing a term.
It parses in three stages:
1. An initial, "atomic" term (`parseExprIni`).
2. A chain of "tight" postfix operators like application `f(x)` (`parseExprArg`).
3. A "loose" infix operator like `+` or `->` (`parseExprOpr`).
The `withOperatorParsing` helper ensures that stages 2 and 3 are skipped
if a "blocked" operator is encountered, resolving grammatical ambiguities.
-}
parseExpr :: Parser Expr
parseExpr = located $ do
  t0 <- parseExprIni
  t1 <- withOperatorParsing t0 parseExprArg
  withOperatorParsing t1 parseExprOpr

{- | Parses a term, temporarily blocking a given operator.
This is useful for parsing expressions where an operator might be ambiguous
in the grammar, e.g., `~ term { ... }` where `term` should not be an
infix expression that includes `{`.
-}
parseExprBefore :: String -> Parser Expr
parseExprBefore op = do
  st <- get
  let wasBlocked = blocked st
  let newBlocked = op : wasBlocked
  put st{blocked = newBlocked}
  -- Use observing to catch parse failures and ensure cleanup
  termResult <- observing parseExpr
  case termResult of
    Left err -> do
      -- Restore blocked state before re-throwing the error
      st' <- get
      put st'{blocked = wasBlocked}
      parseError err
    Right term -> do
      -- Normal restoration path
      st' <- get
      put st'{blocked = wasBlocked}
      return term

-- | Syntax: x, foo, bar_123, Type<A,B>, Nat/add
parseVar :: Parser Expr
parseVar = label "variable" $ do
  n <- name
  case n of
    "Set" -> return Set
    "Empty" -> return Emp
    "Unit" -> return Uni
    "Bool" -> return Bit
    "False" -> return Bt0
    "True" -> return Bt1
    "Nat" -> return Nat
    "U64" -> return (Num U64_T)
    "I64" -> return (Num I64_T)
    "F64" -> return (Num F64_T)
    "Char" -> return (Num CHR_T)
    "U64_TO_CHAR" -> return (Pri U64_TO_CHAR)
    "CHAR_TO_U64" -> return (Pri CHAR_TO_U64)
    "HVM_INC" -> return (Pri HVM_INC)
    "HVM_DEC" -> return (Pri HVM_DEC)
    _ -> return $ Var n 0

-- | Syntax: ()
parseOne :: Parser Expr
parseOne = label "unit value (())" $ symbol "()" >> return One

-- | Syntax: *
parseEra :: Parser Expr
parseEra = label "Eraser" $ symbol "*" >> return Era

-- | Syntax: &L{a,b}
parseSup :: Parser Expr
parseSup = label "superposition" $ do
  l <- try $ do
    _ <- symbol "&"
    l <- parseExprBefore "{"
    _ <- symbol "{"
    return l
  a <- parseExpr
  _ <- symbol ","
  b <- parseExpr
  _ <- symbol "}"
  return $ Sup l a b

-- | Syntax: if condition: trueCase else: falseCase
parseBifIf :: Parser Expr
parseBifIf = label "if clause" $ do
  _ <- try $ keyword "if"
  -- Block ':' so it can't be parsed as a trailing operator
  -- on the scrutinee by downstream postfix/infix parsers.
  condition <- parseExprBefore ":"
  _ <- symbol ":"
  -- Block operator parsing when we hit 'else' to avoid
  -- consuming into the else-branch accidentally.
  trueCase <- parseExprBefore "else"
  _ <- symbol "else"
  _ <- symbol ":"
  falseCase <- parseExpr
  return $ App (BitM falseCase trueCase) condition

-- | Syntax: Σ x: Type. body | any x: Type. body | Σ Type. Type | any Type. Type
parseSig :: Parser Expr
parseSig = label "dependent pair type" $ do
  _ <- try $ choice [symbol "Σ", keyword "any"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseSigSimple
    _ -> do
      _ <- symbol "."
      b <- parseExpr
      return $ foldr (\(x, t) acc -> Sig t (Lam x (Just t) (const acc))) b bindings
 where
  parseBinding = try $ do
    x <- name
    _ <- symbol ":"
    t <- parseExpr
    return (x, t)

{- | Syntax: Type . Type
Simplified form of dependent pair without binding
-}
parseSigSimple :: Parser Expr
parseSigSimple = do
  a <- parseExpr
  _ <- symbol "."
  Sig a <$> parseExpr

-- | Syntax: ∀ x: Type. body | all x: Type. body | ∀ Type. Type | all Type. Type
parseAll :: Parser Expr
parseAll = label "dependent function type" $ do
  _ <- try $ choice [symbol "∀", keyword "all"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseAllSimple
    _ -> do
      _ <- symbol "."
      b <- parseExpr
      return $ foldr (\(x, t) acc -> All t (Lam x (Just t) (const acc))) b bindings
 where
  parseBinding = try $ do
    x <- name
    _ <- symbol ":"
    t <- parseExpr
    return (x, t)

{- | Syntax: Type . Type
Simplified form of dependent function without binding
-}
parseAllSimple :: Parser Expr
parseAllSimple = do
  a <- parseExpr
  _ <- symbol "."
  All a <$> parseExpr

-- Enum Type Parsers
-- -----------------

-- | Syntax: &{tag1, tag2, tag3}
parseEnu :: Parser Expr
parseEnu = label "enum type" $ do
  _ <- try $ do
    _ <- symbol "enum"
    _ <- symbol "{"
    return ()
  s <- sepBy parseSymbolName (symbol ",")
  _ <- symbol "}"
  return (Enu s)

{- | Syntax: &name
Helper for parsing enum tag names
-}
parseSymbolName :: Parser String
parseSymbolName = do
  _ <- symbol "&"
  some (satisfy isNameChar)

-- | Syntax: @tag | @tag{field1, field2} | &tag
parseSym :: Parser Expr
parseSym = label "enum symbol / constructor" $ try $ do
  choice
    [ parseConstructor -- @tag{...} -> (&tag,(fields...))
    , parseNewSymbol -- &tag
    , parseOldSymbol -- @tag -> (&tag,())
    ]
 where
  -- Parse @tag{...} constructor syntax with precise location propagation
  -- We capture two spans:
  -- - spTag: the span of "@tag" (for the &tag symbol)
  -- - spCtor: the span of the whole constructor "@tag{...}" (for the trailing ())
  parseConstructor = try $ do
    (spCtor, (spTag, tag, fields)) <- withSpan $ do
      (spTag, tag) <- withSpan $ do
        _ <- symbol "@"
        some (satisfy isNameChar)
      _ <- symbol "{"
      fs <- sepEndBy parseExpr (symbol ",")
      _ <- symbol "}"
      pure (spTag, tag, fs)
    return $ buildCtorWithSpans spTag spCtor tag fields

  -- Parse new &tag bare symbol syntax
  parseNewSymbol = try $ do
    _ <- char '&'
    notFollowedBy (char '{') -- make sure we are not &{...} enum type
    n <- some (satisfy isNameChar)
    skip
    return $ Sym n

  -- Parse old @tag bare symbol syntax and desugar to (&tag,()) with location on both
  parseOldSymbol = try $ do
    (spTag, tag) <- withSpan $ do
      _ <- symbol "@"
      notFollowedBy (char '{') -- make sure we are not @{...} or @tag{...}
      lexeme $ some (satisfy isNameChar)
    -- Desugar @Foo to (&Foo,()) and attach the span to both the symbol and the unit
    let sym = Loc spTag (Sym tag)
    let one = Loc spTag One
    return $ Tup sym one

  -- Build (&tag, (f1, (f2, ... , Loc spCtor ())))
  buildCtorWithSpans :: Span -> Span -> String -> [Expr] -> Expr
  buildCtorWithSpans spTag spCtor tag fs =
    let end = Loc spCtor One
        tup = foldr Tup end fs
        sym = Loc spTag (Sym tag)
     in Tup sym tup

-- | Syntax: match expr: case pat: body | match expr { case pat: body }
parsePat :: Parser Expr
parsePat = label "pattern match" $ do
  srcPos <- getSourcePos
  _ <- try $ keyword "match"
  scruts <- some $ parseExprBefore ":"
  delim <- choice [':' <$ symbol ":", '{' <$ symbol "{"]
  moves <- concat <$> many parseWith
  clauses <- case delim of
    ':' -> parseIndentClauses (unPos (sourceColumn srcPos)) (length scruts)
    '{' -> parseBraceClauses (length scruts)
    _ -> fail "unreachable"
  when (delim == '{') (void $ symbol "}")
  _ <- optional (symbol ";")
  let pat = Pat scruts moves clauses
  pure pat
 where
  -- Parse 'with' statements
  parseWith = do
    _ <- try $ symbol "with"
    many
      ( do
          x <- try name
          v <- option (Var x 0) (try (symbol "=" >> parseExpr))
          return (x, v)
      )

{- | Syntax: case pattern1 pattern2: body
Indentation-sensitive clause list (stops when out-dented)
-}
parseIndentClauses :: Int -> Int -> Parser [Case]
parseIndentClauses col arity = many clause
 where
  clause = label "case clause" $ do
    pos <- try $ do
      skip
      pos <- getSourcePos
      guard (unPos (sourceColumn pos) >= col)
      _ <- symbol "case"
      return pos
    pats <- replicateM arity (parseExprBefore ":")
    _ <- symbol ":"
    body <- parseExpr
    pure (pats, body)

{- | Syntax: case pattern1 pattern2: body
Braced clause list (runs until the closing '}')
-}
parseBraceClauses :: Int -> Parser [Case]
parseBraceClauses arity = manyTill singleClause (lookAhead (symbol "}"))
 where
  singleClause = label "case clause" $ do
    _ <- symbol "case"
    pats <- replicateM arity (parseExprBefore ":")
    _ <- symbol ":"
    body <- parseExpr
    pure (pats, body)

{- | Syntax: fork L:a else:b
  or: fork L:a elif:b elif:c ... else:d
-}
parseFrk :: Parser Expr
parseFrk = label "fork" $ do
  _ <- try $ symbol "fork"
  -- Block ':' so it can't be parsed as a trailing operator
  -- on the scrutinee by downstream postfix/infix parsers.
  l <- parseExprBefore ":"
  _ <- symbol ":"
  -- Parse first branch; prevent it from consuming the following 'else'.
  a <- parseExprBefore "else"
  elifs <- many parseElif
  _ <- symbol "else"
  _ <- symbol ":"
  buildForkChain l a elifs <$> parseExpr
 where
  parseElif :: Parser Expr
  parseElif = do
    _ <- keyword "elif"
    _ <- symbol ":"
    -- Parse elif branch; avoid consuming the subsequent 'else'.
    parseExprBefore "else"

  buildForkChain :: Expr -> Expr -> [Expr] -> Expr -> Expr
  buildForkChain l firstBranch [] elseBranch = Frk l firstBranch elseBranch
  buildForkChain l firstBranch (elif : elifs) elseBranch =
    Frk l firstBranch (buildForkChain l elif elifs elseBranch)

-- | Syntax: log string expr
parseLog :: Parser Expr
parseLog = label "log" $ do
  _ <- try $ keyword "log"
  s <- parseExpr
  Log s <$> parseExpr

-- | Syntax: trust term
parseTrust :: Parser Expr
parseTrust = label "trust" $ do
  _ <- try $ keyword "trust"
  Tst <$> parseExpr

-- | Syntax: view(functionName)
parseView :: Parser Expr
parseView = label "view" $ do
  try $ do
    _ <- symbol "view"
    _ <- symbol "("
    return ()
  nam <- name
  _ <- symbol ")"
  return $ Var (nam ++ "$") 0

-- | Syntax: []
parseNil :: Parser Expr
parseNil = label "empty list ([])" $ symbol "[]" >> return Nil

-- | Syntax: Nat
parseNat :: Parser Expr
parseNat = label "natural number type (Nat)" $ try $ do
  _ <- symbol "Nat"
  notFollowedBy (satisfy isNameChar)
  return Nat

-- | Syntax: 1n, 2n, 3n, 42n, 123n
parseNatLit :: Parser Expr
parseNatLit = label "natural number literal" $ try $ do
  -- Parse digits manually to avoid L.decimal consuming too much
  digits <- some digitChar
  _ <- char 'n'
  skip -- consume whitespace after 'n'
  let n = read digits :: Integer
      build 0 = Zer
      build k = Suc (build (k - 1))
  return (build n)

{- | Parse numeric literals:
| 123    -> U64 (unsigned)
| +123   -> I64 (signed positive)
| -123   -> I64 (signed negative)
| 123.0  -> F64 (floating point)
-}
parseNumLit :: Parser Expr
parseNumLit =
  label "numeric literal" $
    choice
      [ try parseFloatLit -- Try float first (because 123.0 starts like 123)
      , try parseSignedLit -- Try signed next (because +123 starts with a sign)
      , parseUnsignedLit -- Finally unsigned
      ]

-- | Parse floating point: 123.0, -45.67, +3.14, 0xFF.0, 0b101.0
parseFloatLit :: Parser Expr
parseFloatLit = do
  sign <- optional (char '+' <|> char '-')
  intPart <- parseUnsignedNumber
  _ <- char '.'
  fracPart <- some digitChar
  skip
  let signStr = maybe "" (: []) sign
      floatStr = signStr ++ show intPart ++ "." ++ fracPart
      floatVal = read floatStr :: Double
  return $ Val (F64_V floatVal)

-- | Parse signed integer: +123, -456, +0x123, -0xABC, +0b101, -0b110
parseSignedLit :: Parser Expr
parseSignedLit = do
  sign <- char '+' <|> char '-'
  n <- parseUnsignedNumber
  skip
  let value = if sign == '-' then -(fromIntegral n) else fromIntegral n
  return $ Val (I64_V value)

-- | Parse a raw unsigned number (decimal, hex, or binary)
parseUnsignedNumber :: Parser Word64
parseUnsignedNumber =
  choice
    [ try $ string "0x" >> L.hexadecimal
    , try $ do
        _ <- string "0b"
        digits <- some (char '0' <|> char '1')
        return $ foldl (\acc d -> acc * 2 + if d == '1' then 1 else 0) 0 digits
    , L.decimal
    ]

-- | Parse unsigned integer: 123, 0x123, 0b101
parseUnsignedLit :: Parser Expr
parseUnsignedLit = lexeme $ do
  n <- parseUnsignedNumber
  -- Make sure we don't have 'n' suffix (that would be a Nat literal)
  notFollowedBy (char 'n')
  return $ Val (U64_V n)

-- | Parse character literal: 'x', '\n', '\t', etc.
parseCharLit :: Parser Expr
parseCharLit = label "character literal" $ lexeme $ do
  _ <- char '\''
  c <- parseChar
  _ <- char '\''
  return $ Val (CHR_V c)
 where
  parseChar =
    choice
      [ parseEscaped
      , satisfy (\c -> c /= '\'' && c /= '\\')
      ]

  parseEscaped = do
    _ <- char '\\'
    choice
      [ char 'n' >> return '\n'
      , char 't' >> return '\t'
      , char 'r' >> return '\r'
      , char '0' >> return '\0'
      , char '\\' >> return '\\'
      , char '\'' >> return '\''
      , char '"' >> return '"'
      , parseUnicodeEscape
      ]

  parseUnicodeEscape = do
    _ <- char 'u'
    digits <- replicateM 4 (satisfy (\c -> isDigit c || c `elem` "abcdefABCDEF"))
    let code = read ("0x" ++ digits) :: Int
    return $ toEnum code

{- | Parse string literal: "hello\nworld"
Desugars to: 'h' <> 'e' <> 'l' <> 'l' <> 'o' <> '\n' <> 'w' <> 'o' <> 'r' <> 'l' <> 'd' <> []
-}
parseStringLit :: Parser Expr
parseStringLit = label "string literal" $ lexeme $ do
  _ <- char '"'
  chars <- many parseStringChar
  _ <- char '"'
  return $ foldr (Con . Val . CHR_V) Nil chars
 where
  parseStringChar =
    choice
      [ parseStringEscaped
      , satisfy (\c -> c /= '"' && c /= '\\')
      ]

  parseStringEscaped = do
    _ <- char '\\'
    choice
      [ char 'n' >> return '\n'
      , char 't' >> return '\t'
      , char 'r' >> return '\r'
      , char '0' >> return '\0'
      , char '\\' >> return '\\'
      , char '\'' >> return '\''
      , char '"' >> return '"'
      , parseStringUnicodeEscape
      ]

  parseStringUnicodeEscape = do
    _ <- char 'u'
    digits <- replicateM 4 (satisfy (\c -> isDigit c || c `elem` "abcdefABCDEF"))
    let code = read ("0x" ++ digits) :: Int
    return $ toEnum code

-- | Parse numeric unary operations: not x, -x
parseNumUna :: Parser Expr
parseNumUna = label "numeric unary operation" $ do
  op <-
    choice
      [ try $ keyword "not" >> return NOT
      , try $ symbol "-" >> return NEG
      ]
  Op1 op <$> parseExpr

-- | Syntax: [term1, term2, term3]
parseLstLit :: Parser Expr
parseLstLit = label "list literal" $ do
  _ <- try $ symbol "["
  terms <- sepEndBy parseExpr (symbol ",")
  _ <- symbol "]"
  return $ foldr Con Nil terms

-- | Syntax: return term
parseReturn :: Parser Expr
parseReturn = label "return statement" $ do
  _ <- try $ keyword "return"
  parseExpr

-- | Syntax: {==} | finally
parseRfl :: Parser Expr
parseRfl =
  label "reflexivity ({==} or finally)" $
    choice
      [ parseBraces
      , parseFinally
      ]
 where
  parseBraces = do
    _ <- try $ do
      _ <- symbol "{"
      _ <- symbol "=="
      return ()
    _ <- symbol "}"
    return Rfl

  parseFinally = do
    _ <- try $ keyword "finally"
    return Rfl

-- | Syntax: rewrite expr body
parseRewrite :: Parser Expr
parseRewrite = label "rewrite" $ do
  _ <- try $ keyword "rewrite"
  e <- parseExpr
  Rwt e <$> parseExpr

{- | Syntax: absurd expr
Desugars to: match expr {}
-}
parseAbsurd :: Parser Expr
parseAbsurd = label "absurd" $ do
  _ <- try $ keyword "absurd"
  scrut <- parseExpr
  return (Pat [scrut] [] [])

{- | Syntax: (term1, term2) | (f arg1 arg2)
Disambiguates between tuples and applications
-}
parseTupApp :: Parser Expr
parseTupApp = do
  _ <- try $ symbol "("
  choice [parseTup, parseApp]

-- | Syntax: (function arg1 arg2 arg3)
parseApp :: Parser Expr
parseApp = label "application" $ do
  f <- parseExpr
  xs <- many parseExpr
  _ <- symbol ")"
  return (foldl App f xs)

-- | Syntax: function<arg1, arg2, arg3>
parsePol :: Expr -> Parser Expr
parsePol f = label "polymorphic application" $ try $ do
  _ <- try $ do
    _ <- symbol "<"
    notFollowedBy (char '>')
  args <- sepEndBy parseExpr (symbol ",")
  _ <- symbol ">"
  return $ foldl App f args

-- | Syntax: function(arg1, arg2, arg3)
parseCal :: Expr -> Parser Expr
parseCal f = label "function application" $ try $ do
  _ <- symbol "("
  args <- sepEndBy parseExpr (symbol ",")
  _ <- symbol ")"
  return $ foldl App f args

-- | trailing‐operator parsers

-- | Syntax: (term1, term2) | (term1, term2, term3)
parseTup :: Parser Expr
parseTup = label "pair" $ try $ do
  terms <- try $ do
    first <- parseExpr
    _ <- symbol ","
    rest <- sepBy1 parseExpr (symbol ",")
    return (first : rest)
  _ <- symbol ")"
  case terms of
    [] -> fail "empty tuple"
    [x] -> fail "single element tuple"
    xs -> return $ foldr1 Tup xs

-- | Syntax: head <> tail
parseCon :: Expr -> Parser Expr
parseCon t = label "list cons" $ do
  s <- get
  _ <- try $ symbol "<>"
  Con t <$> parseExpr

-- | Syntax: InputType -> OutputType
parseFun :: Expr -> Parser Expr
parseFun t = label "function type" $ do
  _ <- try $ symbol "->"
  All t . Lam "_" (Just t) . const <$> parseExpr

-- | Syntax: Type1 & Type2
parseAnd :: Expr -> Parser Expr
parseAnd t = label "product type" $ do
  _ <- try $ symbol "&"
  Sig t . Lam "_" (Just t) . const <$> parseExpr

-- | Syntax: term :: Type
parseChk :: Expr -> Parser Expr
parseChk x = label "type check" $ do
  _ <- try $ symbol "::"
  Chk x <$> parseExpr

-- | Syntax: ElementType[]
parseLst :: Expr -> Parser Expr
parseLst t = label "list type" $ do
  _ <- try $ symbol "[]"
  return (Lst t)

-- | Syntax: Type{term1 == term2} or Type{term1 != term2}
parseEql :: Expr -> Parser Expr
parseEql t = label "equality type" $ do
  _ <- try $ symbol "{"
  a <- parseExpr
  op <-
    choice
      [ symbol "==" >> return True
      , symbol "!=" >> return False
      ]
  b <- parseExpr
  _ <- symbol "}"
  let eql = Eql t a b
  return $ if op then eql else App (Ref "Not" 1) eql

-- | Parse numeric binary operations
parseNumOp :: Expr -> Parser Expr
parseNumOp lhs = label "numeric operation" $ do
  st <- get
  op <-
    choice $
      concat
        [ guard (not (tight st))
            >> [ try $ symbol "<=" >> return LEQ
               , try $ symbol ">=" >> return GEQ
               , try $ symbol "<<" >> return SHL
               , try $ symbol ">>" >> return SHR
               , try $ symbol ">" >> return GRT
               , try $ do
                   _ <- symbol "<"
                   notFollowedBy (char '>')
                   return LST
               ]
        ,
          [ try $ symbol "===" >> return EQL
          , try $ symbol "!==" >> return NEQ
          , try $ keyword "and" >> return AND
          , try $ keyword "or" >> return OR
          , try $ keyword "xor" >> return XOR
          , try $ symbol "**" >> return POW
          , try $ symbol "-" >> return SUB
          , try $ symbol "*" >> return MUL
          , try $ symbol "/" >> return DIV
          , try $ symbol "%" >> return MOD
          , try $ symbol "^" >> return XOR
          ]
        ]
  rhs <- parseExpr
  return $ Op2 op lhs rhs

-- | Syntax: 3n + x (Nat successor) or x + y (numeric addition)
parseAdd :: Expr -> Parser Expr
parseAdd t = label "addition" $ do
  _ <- try $ symbol "+"
  b <- parseExpr
  case cut t of
    -- If LHS is a Nat literal, interpret as successor(s)
    n | isNatLit n -> return (applySuccessors (countSuccessors n) b)
    -- Otherwise, it's numeric addition
    _ -> return (Op2 ADD t b)
 where
  isNatLit :: Expr -> Bool
  isNatLit Zer = True
  isNatLit (Suc n) = isNatLit n
  isNatLit (Loc _ t) = isNatLit t
  isNatLit _ = False

  -- Count number of successors
  countSuccessors :: Expr -> Int
  countSuccessors Zer = 0
  countSuccessors (Suc n) = 1 + countSuccessors n
  countSuccessors (Loc _ t) = countSuccessors t
  countSuccessors _ = 0

  applySuccessors :: Int -> Expr -> Expr
  applySuccessors 0 t = t
  applySuccessors n t = Suc (applySuccessors (n - 1) t)

{- | Syntax: var = value; body | pattern = value; body
Interprets as let if t is a variable, otherwise as pattern match
-}
parseAss :: Expr -> Parser Expr
parseAss t = label "location binding" $ do
  mtyp <- try $ do
    mtyp <- optional $ do
      _ <- symbol ":"
      parseExprBefore "="
    _ <- symbol "="
    notFollowedBy (char '=')
    return mtyp
  -- Check for invalid assignment patterns after confirming it's an assignment
  case cut t of
    Bit -> fail "Cannot assign a value to `Bool` native type"
    Nat -> fail "Cannot assign a value to `Nat` native type"
    Set -> fail "Cannot assign a value to `Set` native type"
    Emp -> fail "Cannot assign a value to `Empty` native type"
    Uni -> fail "Cannot assign a value to `Unit` native type"
    Bt0 -> fail "Cannot assign a value to `False` boolean literal"
    Bt1 -> fail "Cannot assign a value to `True` boolean literal"
    Zer -> fail "Cannot assign a value to `0n` nat literal"
    Suc _ -> fail "Cannot assign a value to nat literal"
    Num nt -> fail $ "Cannot assign a value to `" ++ show (Num nt) ++ "` numeric type"
    Val v -> fail $ "Cannot assign a value to `" ++ show (Val v) ++ "` literal"
    One -> fail "Cannot assign a value to `()` unit literal"
    Nil -> fail "Cannot assign a value to `[]` list literal"
    Rfl -> fail "Cannot assign a value to `{==}` reflexivity literal"
    Era -> fail "Cannot assign a value to `*` eraser"
    Var x _ -> do
      v <- parseExpr
      _ <- parseSemi
      b <- expectBody "assignment" parseExpr
      return $ Let x mtyp v (const b)
    _ -> do
      v <- parseExpr
      _ <- parseSemi
      b <- expectBody "assignment" parseExpr
      return $ Pat [v] [] [([t], b)]

-- | HOAS‐style binders

-- | Syntax: λ x y z. body | lam x y z. body | λ (x,y) z. body
parseLam :: Parser Expr
parseLam = label "lambda abstraction" $ do
  _ <- try $ do
    _ <- choice [symbol "λ", keyword "lambda"]
    notFollowedBy (symbol "{")
    return ()
  -- Parse terms instead of just names to support patterns
  -- pats <- some parseExpr
  binders <- some $ do
    pat <- parseExprBefore ":"
    mtyp <- optional $ do
      _ <- symbol ":"
      parseExpr
    return (pat, mtyp)
  _ <- symbol "."
  body <- parseExpr
  -- Desugar pattern lambdas
  return $ foldr desugarLamPat body (zip [0 ..] binders)
 where
  desugarLamPat :: (Int, (Expr, Maybe Expr)) -> Expr -> Expr
  desugarLamPat (_, (cut -> (Var x _), mtyp)) acc = Lam x mtyp (const acc)
  desugarLamPat (idx, (pat, mtyp)) acc =
    -- Generate a fresh variable name using index
    let freshVar = "_" ++ show idx
     in Lam freshVar mtyp (\_ -> Pat [Var freshVar 0] [] [([pat], acc)])

-- | Syntax: μ f. body
parseFix :: Parser Expr
parseFix = label "fixed point" $ do
  _ <- try $ symbol "μ"
  k <- name
  _ <- symbol "."
  Fix k . const <$> parseExpr

-- | Parse λ-match forms: λ{...}
parseLamMatch :: Parser Expr
parseLamMatch = label "lambda match" $ do
  _ <- try $ do
    _ <- choice [symbol "λ", keyword "lambda"]
    _ <- symbol "{"
    return ()
  -- Check for empty match first
  mb_close <- optional (lookAhead (symbol "}"))
  case mb_close of
    Just _ -> do
      _ <- symbol "}"
      return EmpM
    Nothing -> do
      term <-
        choice
          [ parseUniMForm
          , parseBitMForm
          , parseNatMForm
          , parseLstMForm
          , parseSigMForm
          , parseEnuMForm
          , parseSupMForm
          ]
      _ <- symbol "}"
      return term
 where
  -- λ{(): term}
  parseUniMForm = do
    _ <- try $ do
      _ <- symbol "()"
      _ <- symbol ":"
      return ()
    f <- parseExpr
    _ <- parseSemi
    return (UniM f)

  -- λ{False: term; True: term}
  parseBitMForm = do
    _ <- try $ do
      _ <- symbol "False"
      _ <- symbol ":"
      return ()
    f <- parseExpr
    _ <- parseSemi
    _ <- symbol "True"
    _ <- symbol ":"
    t <- parseExpr
    _ <- parseSemi
    return (BitM f t)

  -- λ{0n: term; 1n+: term}
  parseNatMForm = do
    _ <- try $ do
      _ <- symbol "0n"
      _ <- symbol ":"
      return ()
    z <- parseExpr
    _ <- parseSemi
    _ <- symbol "1n+"
    _ <- symbol ":"
    s <- parseExpr
    _ <- parseSemi
    return (NatM z s)

  -- λ{[]: term; <>: term}
  parseLstMForm = do
    _ <- try $ do
      _ <- symbol "[]"
      _ <- symbol ":"
      return ()
    n <- parseExpr
    _ <- parseSemi
    _ <- symbol "<>"
    _ <- symbol ":"
    c <- parseExpr
    _ <- parseSemi
    return (LstM n c)

  -- λ{(,): term}
  parseSigMForm = do
    _ <- try $ do
      _ <- symbol "(,)"
      _ <- symbol ":"
      return ()
    f <- parseExpr
    _ <- parseSemi
    return (SigM f)

  -- λ{&tag1: term1; &tag2: term2; ...; default}
  parseEnuMForm = do
    _ <- try (lookAhead (choice [symbol "@", symbol "&"]))
    cases <- many $ try $ do
      _ <- choice [symbol "@", symbol "&"]
      s <- some (satisfy isNameChar)
      _ <- symbol ":"
      t <- parseExpr
      _ <- parseSemi
      return (s, t)
    def <- option One $ try $ do
      notFollowedBy (symbol "}")
      notFollowedBy (symbol "@")
      notFollowedBy (symbol "&")
      term <- parseExpr
      _ <- parseSemi
      return term
    return (EnuM cases def)

  -- λ{&L{,}: term}
  parseSupMForm = do
    l <- try $ do
      _ <- symbol "&"
      l <- parseExprBefore "{"
      _ <- symbol "{"
      _ <- symbol ","
      _ <- symbol "}"
      _ <- symbol ":"
      return l
    f <- parseExpr
    _ <- parseSemi
    return (SupM l f)

-- | Syntax: ~{term} | ~term | ~ term { cases... }
parseTildeExpr :: Parser Expr
parseTildeExpr = label "tilde expression (induction or match)" $ do
  _ <- try $ symbol "~"
  choice
    [ -- ~ term [{...}]
      do
        scrut <- parseExprBefore "{"
        is_match <- optional (lookAhead (symbol "{"))
        case is_match of
          Just _ -> do
            -- It's a match expression
            _ <- symbol "{"
            -- Check for empty pattern match first
            mb_close <- optional (lookAhead (symbol "}"))
            case mb_close of
              Just _ -> do
                _ <- symbol "}"
                return (App EmpM scrut)
              Nothing -> do
                term <-
                  choice
                    [ parseUniMCases scrut
                    , parseBitMCases scrut
                    , parseNatMCases scrut
                    , parseLstMCases scrut
                    , parseSigMCases scrut
                    , parseEnuMCases scrut
                    , parseSupMCases scrut
                    ]
                _ <- symbol "}"
                return term
          Nothing -> fail "Expected match expression after ~"
    ]

-- Case parsers for expression-based matches
-- -----------------------------------------

-- | Syntax: (): term;
parseUniMCases :: Expr -> Parser Expr
parseUniMCases scrut = do
  _ <- try $ do
    _ <- symbol "()"
    _ <- symbol ":"
    return ()
  f <- parseExpr
  _ <- parseSemi
  return (App (UniM f) scrut)

-- | Syntax: False: term; True: term;
parseBitMCases :: Expr -> Parser Expr
parseBitMCases scrut = do
  _ <- try $ do
    _ <- symbol "False"
    _ <- symbol ":"
    return ()
  f <- parseExpr
  _ <- parseSemi
  _ <- symbol "True"
  _ <- symbol ":"
  t <- parseExpr
  _ <- parseSemi
  return (App (BitM f t) scrut)

-- | Syntax: 0n: term; 1n+: term;
parseNatMCases :: Expr -> Parser Expr
parseNatMCases scrut = do
  _ <- try $ do
    _ <- symbol "0n"
    _ <- symbol ":"
    return ()
  z <- parseExpr
  _ <- parseSemi
  _ <- symbol "1n+"
  _ <- symbol ":"
  s <- parseExpr
  _ <- parseSemi
  return (App (NatM z s) scrut)

-- | Syntax: []: term; <>: term;
parseLstMCases :: Expr -> Parser Expr
parseLstMCases scrut = do
  _ <- try $ do
    _ <- symbol "[]"
    _ <- symbol ":"
    return ()
  n <- parseExpr
  _ <- parseSemi
  _ <- symbol "<>"
  _ <- symbol ":"
  c <- parseExpr
  _ <- parseSemi
  return (App (LstM n c) scrut)

-- | Syntax: (,): term;
parseSigMCases :: Expr -> Parser Expr
parseSigMCases scrut = do
  _ <- try $ do
    _ <- symbol "(,)"
    _ <- symbol ":"
    return ()
  f <- parseExpr
  _ <- parseSemi
  return (App (SigM f) scrut)

-- | Syntax: &tag1: term1; &tag2: term2; ...; default; (also accepts @tag for compatibility)
parseEnuMCases :: Expr -> Parser Expr
parseEnuMCases scrut = do
  _ <- try (lookAhead (choice [symbol "@", symbol "&"]))
  cases <- many $ try $ do
    _ <- choice [symbol "@", symbol "&"]
    s <- some (satisfy isNameChar)
    _ <- symbol ":"
    t <- parseExpr
    _ <- parseSemi
    return (s, t)
  def <- option One $ try $ do
    notFollowedBy (symbol "}")
    notFollowedBy (symbol "@")
    notFollowedBy (symbol "&")
    term <- parseExpr
    _ <- parseSemi
    return term
  return (App (EnuM cases def) scrut)

-- | Syntax: &L{,}: term;
parseSupMCases :: Expr -> Parser Expr
parseSupMCases scrut = do
  l <- try $ do
    _ <- symbol "&"
    l <- parseExprBefore "{"
    _ <- symbol "{"
    _ <- symbol ","
    _ <- symbol "}"
    _ <- symbol ":"
    return l
  f <- parseExpr
  _ <- parseSemi
  return (App (SupM l f) scrut)

-- | Main entry points

-- | Parse a term from a string, returning an error message on failure
doParseExpr :: FilePath -> String -> Either String Expr
doParseExpr file input =
  case evalState (runParserT p file input) (ParserState True input [] M.empty 0) of
    Left err -> Left (formatError input err)
    Right res -> Right (adjust (Book M.empty []) res)
 where
  p = do
    skip
    t <- parseExpr
    skip
    eof
    return t

-- | Parse a term from a string, crashing on failure
doReadExpr :: String -> Expr
doReadExpr input =
  case doParseExpr "<input>" input of
    Left err -> error err
    Right res -> res
