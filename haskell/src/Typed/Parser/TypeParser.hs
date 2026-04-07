module Typed.Parser.TypeParser
  ( parseTy
  , parseTyAtom
  , parseTyFull
  , tyReserved
  ) where

import Data.Void
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Typed.Syntax.Type

type Parser = Parsec Void String

-- Lexer helpers (exported for reuse)

sc :: Parser ()
sc = L.space space1
            (L.skipLineComment "--")
            (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

tyReserved :: [String]
tyReserved = ["Top", "Bot"]

-- Type grammar

parseTy :: Parser Ty
parseTy = do
  t <- parseTySum
  option t ((TyArr t) <$> (arrow *> parseTy))
  where
    arrow = void (symbol "->") <|> void (symbol "→")

parseTySum :: Parser Ty
parseTySum = do
  t  <- parseTyProd
  ts <- many (symbol "+" *> parseTyProd)
  return $ foldl TySum t ts

parseTyProd :: Parser Ty
parseTyProd = do
  t  <- parseTyAtom
  ts <- many (cross *> parseTyAtom)
  return $ foldl TyProd t ts
  where
    cross = void (symbol "*") <|> void (symbol "×")

parseTyAtom :: Parser Ty
parseTyAtom
    =  (TyUnit <$ (symbol "Top" <|> symbol "⊤"))
   <|> (TyVoid <$ (symbol "Bot" <|> symbol "⊥"))
   <|> (TyVar  <$> upperIdent)
   <|> between (symbol "(") (symbol ")") parseTy

upperIdent :: Parser String
upperIdent = lexeme $ try $ do
  c  <- upperChar
  cs <- many (alphaNumChar <|> char '_')
  return (c : cs)

parseTyFull :: String -> Either (ParseErrorBundle String Void) Ty
parseTyFull input = parse (sc *> parseTy <* eof) "<type>" input
