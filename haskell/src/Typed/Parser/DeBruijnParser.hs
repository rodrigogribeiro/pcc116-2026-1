module Typed.Parser.DeBruijnParser
  ( parseTerm
  , parseFull
  ) where

import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad (void)

import Typed.Syntax.Type
import Typed.Syntax.DeBruijn
import Typed.Parser.TypeParser (parseTy)

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

-- Term grammar

parseTerm :: Parser Term
parseTerm = sc *> parseExpr

parseExpr :: Parser Term
parseExpr = parseLam <|> parseCase <|> parseAnnotated

parseLam :: Parser Term
parseLam = do
  void $ lexeme (char '\\' <|> char 'λ')
  void $ symbol ":"
  ty   <- parseTy
  void $ symbol "."
  Lam ty <$> parseExpr

parseCase :: Parser Term
parseCase = do
  void $ symbol "case"
  t  <- parseApp
  void $ symbol "of"
  void $ symbol "("
  void $ symbol "inl"
  void $ symbol "=>"
  t1 <- parseExpr
  void $ symbol "|"
  void $ symbol "inr"
  void $ symbol "=>"
  t2 <- parseExpr
  void $ symbol ")"
  return (TmCase t t1 t2)

parseAnnotated :: Parser Term
parseAnnotated = do
  t <- parseApp
  option t (do
    void $ symbol "as"
    ty <- parseTy
    case t of
      TmInl inner _    -> return (TmInl inner ty)
      TmInr inner _    -> return (TmInr inner ty)
      TmAbsurd inner _ -> return (TmAbsurd inner ty)
      _                -> return t)

parseApp :: Parser Term
parseApp = foldl1 App <$> some parseAtom

parseAtom :: Parser Term
parseAtom
    =  (TmUnit <$ symbol "unit")
   <|> parsePairOrParens
   <|> (TmFst   <$> (symbol "fst"    *> parseAtom))
   <|> (TmSnd   <$> (symbol "snd"    *> parseAtom))
   <|> (TmInl   <$> (symbol "inl"    *> parseAtom) <*> pure TyUnit)
   <|> (TmInr   <$> (symbol "inr"    *> parseAtom) <*> pure TyUnit)
   <|> (TmAbsurd <$> (symbol "absurd" *> parseAtom) <*> pure TyUnit)
   <|> (Var     <$> lexeme L.decimal)

parsePairOrParens :: Parser Term
parsePairOrParens =
  between (symbol "(") (symbol ")") $ do
    t <- parseExpr
    option t (do
      void $ symbol ","
      t2 <- parseExpr
      return (TmPair t t2))

-- Entry point

parseFull :: String -> Either (ParseErrorBundle String Void) Term
parseFull input = parse (parseTerm <* eof) "<input>" input
