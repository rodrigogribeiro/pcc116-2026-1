module Untyped.Parser.NamedParser
  ( parseTerm
  , parseFull
  ) where

import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Untyped.Syntax.Named

type Parser = Parsec Void String

-- Lexer

sc :: Parser ()
sc = L.space space1
            (L.skipLineComment "--")
            (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

-- Identifier

identifier :: Parser String
identifier = lexeme $ do
  c  <- letterChar
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  return (c : cs)

-- Term parsers

parseTerm :: Parser Term
parseTerm = sc *> parseApp

parseApp :: Parser Term
parseApp = foldl1 App <$> some parseAtom

parseAtom :: Parser Term
parseAtom = parseLam <|> parseVar <|> parseParens

parseLam :: Parser Term
parseLam = do
  _ <- lexeme (char '\\' <|> char 'λ')
  vars <- some identifier
  _ <- symbol "."
  body <- parseTerm
  return $ foldr Lam body vars

parseVar :: Parser Term
parseVar = Var <$> identifier

parseParens :: Parser Term
parseParens = between (symbol "(") (symbol ")") parseTerm

-- Entry point

parseFull :: String -> Either (ParseErrorBundle String Void) Term
parseFull input = parse (parseTerm <* eof) "<input>" input
