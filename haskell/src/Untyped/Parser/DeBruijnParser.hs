module Untyped.Parser.DeBruijnParser
  ( parseTerm
  , parseFull
  ) where

import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Untyped.Syntax.DeBruijn

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
  _ <- symbol "."
  Lam <$> parseTerm

parseVar :: Parser Term
parseVar = Var <$> lexeme L.decimal

parseParens :: Parser Term
parseParens = between (symbol "(") (symbol ")") parseTerm

-- Entry point

parseFull :: String -> Either (ParseErrorBundle String Void) Term
parseFull input = parse (parseTerm <* eof) "<input>" input
