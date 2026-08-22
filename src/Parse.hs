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

-- Prolog term parser
parseTerm :: Parser Term
parseTerm = try parseList <|> try parseNot <|> try parseParen <|> parseTermAtom

parseNot :: Parser Term
parseNot = do
  _ <- string "\\+" <* ws
  t <- parseTerm
  return (Not t)

parseParen :: Parser Term
parseParen = symbol "(" *> parseTerm <* symbol ")"

parseTermAtom :: Parser Term
parseTermAtom = do
  t <- try parseVar <|> parseAtomOrFunc
  option t $ try $ do
    op <- symbol "="
    rhs <- parseTerm
    return (Func op [t, rhs])

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
  c <- lower <|> char '\''
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
  items <- parseTermAtom `sepBy` comma
  tail' <- optionMaybe (pipe *> parseTermAtom)
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
