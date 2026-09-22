-- | Parsec-based parser for Prolog terms and clause databases.
-- Supports operator-precedence expressions, list notation, and negation.
module Parse
       ( parseProg
       , parseTerm
       ) where

import Text.ParserCombinators.Parsec
import Term

-- Character-level parsers (no token layer)
ws :: Parser ()
ws = skipMany (oneOf " \t\n\r")

symbol :: String -> Parser String
symbol s = try (string s <* ws)

parens :: Parser a -> Parser a
parens p = symbol "(" *> p <* symbol ")"

comma :: Parser String
comma = symbol ","

dot :: Parser String
dot = symbol "."

arrow :: Parser String
arrow = symbol ":-"

pipe :: Parser String
pipe = symbol "|"

-- Prolog term parser with operator precedence
parseTerm :: Parser Term
parseTerm = try parseList <|> try parseNot <|> try parseParen <|> parseExpr

parseNot :: Parser Term
parseNot = do
  _ <- string "\\+" <* ws
  t <- parseTerm
  return (Not t)

parseParen :: Parser Term
parseParen = symbol "(" *> parseTerm <* symbol ")"

-- Expression parser with precedence climbing
parseExpr :: Parser Term
parseExpr = do
  lhs <- parseExpr2
  option lhs $ try $ do
    op <- parseCompOp
    rhs <- parseExpr2
    return (Func op [lhs, rhs])

-- | Left-associative precedence-climbing: repeatedly extend `lhs` with
-- `op [lhs, rhs]` as long as the operator and next operand keep matching.
chainOp :: Parser String -> Parser Term -> Term -> Parser Term
chainOp opP nextP lhs = option lhs $ try $ do
  op <- opP
  rhs <- nextP
  chainOp opP nextP (Func op [lhs, rhs])

parseExpr2 :: Parser Term
parseExpr2 = parseExpr1 >>= chainOp (symbol "+" <|> symbol "-") parseExpr1

parseExpr1 :: Parser Term
parseExpr1 = parsePrimary >>= chainOp (symbol "*" <|> symbol "/" <|> symbol "mod") parsePrimary

parsePrimary :: Parser Term
parsePrimary = try parseList <|> try parseNot <|> try parseParen <|> try parseNegNum <|> try parseVar <|> parseAtomOrFunc

parseNegNum :: Parser Term
parseNegNum = do
  _ <- char '-' <* ws
  n <- many1 digit
  ws
  return (Atom ('-' : n))

parseCompOp :: Parser String
parseCompOp = try (symbol "=\\=")
          <|> try (symbol "=:=")
          <|> try (symbol "=<")
          <|> try (symbol ">=")
          <|> try (symbol "<")
          <|> try (symbol ">")
          <|> try (symbol "is")
          <|> symbol "="

parseAtomOrFunc :: Parser Term
parseAtomOrFunc = do
  name <- parseName
  ws
  args <- option [] (parens (parseTerm `sepBy1` comma))
  return $ case args of
    [] -> Atom name
    _  -> Func name args

parseName :: Parser String
parseName = do
  c <- lower <|> digit <|> char '\''
  if c == '\''
    then do
      s <- many1 (noneOf "'")
      _ <- char '\''
      return s
    else do
      cs <- many (lower <|> digit <|> char '_')
      return (c : cs)

parseVar :: Parser Term
parseVar = do
  c <- upper <|> char '_'
  cs <- many (lower <|> upper <|> digit <|> char '_')
  ws
  return (Var (c : cs))

parseList :: Parser Term
parseList = do
  _ <- symbol "["
  items <- parseTerm `sepBy` comma
  tail' <- optionMaybe (pipe *> parseTerm)
  _ <- symbol "]"
  return $ case (items, tail') of
    ([], Nothing)  -> nil
    ([], Just t)   -> t
    (xs, Nothing)  -> list xs
    (xs, Just t)   -> foldr cons t xs

parseClause :: Parser Clause
parseClause = do
  ws
  head' <- parseTerm
  body <- optionMaybe (arrow *> parseBody)
  _ <- dot
  return $ case body of
    Nothing    -> Simple head'
    Just goals -> head' :- goals

parseBody :: Parser [Term]
parseBody = parseTerm `sepBy1` comma

parseProg :: String -> Either ParseError Prolog
parseProg = parse (many parseClause <* eof) "<input>"
