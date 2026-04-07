module Typed.Parser.NamedParser
  ( parseTerm
  , parseFull
  ) where

import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad (void)

import Typed.Syntax.Type
import Typed.Syntax.Named
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

reservedWords :: [String]
reservedWords =
  [ "unit", "fst", "snd", "inl", "inr", "as", "case", "of", "absurd"
  , "Top", "Bot"
  ]

identifier :: Parser String
identifier = lexeme $ try $ do
  c  <- lowerChar
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reservedWords
    then fail $ "reserved word: " ++ name
    else return name

-- Term grammar

parseTerm :: Parser Term
parseTerm = sc *> parseExpr

parseExpr :: Parser Term
parseExpr = parseLam <|> parseCase <|> parseAnnotated

parseLam :: Parser Term
parseLam = do
  void $ lexeme (char '\\' <|> char 'λ')
  binders <- some parseBinder
  void $ symbol "."
  body <- parseExpr
  return $ foldr (\(x, ty) t -> Lam x ty t) body binders

parseBinder :: Parser (String, Ty)
parseBinder = betweenParens go <|> go
  where
    go = do
      x  <- identifier
      void $ symbol ":"
      ty <- parseTy
      return (x, ty)
    betweenParens = between (symbol "(") (symbol ")")

parseCase :: Parser Term
parseCase = do
  void $ symbol "case"
  t  <- parseApp
  void $ symbol "of"
  void $ symbol "("
  void $ symbol "inl"
  x  <- identifier
  void $ symbol "=>"
  t1 <- parseExpr
  void $ symbol "|"
  void $ symbol "inr"
  y  <- identifier
  void $ symbol "=>"
  t2 <- parseExpr
  void $ symbol ")"
  return (TmCase t x t1 y t2)

parseAnnotated :: Parser Term
parseAnnotated = do
  t <- parseApp
  option t (do
    void $ symbol "as"
    ty <- parseTy
    case t of
      TmInl inner _   -> return (TmInl inner ty)
      TmInr inner _   -> return (TmInr inner ty)
      TmAbsurd inner _ -> return (TmAbsurd inner ty)
      _               -> return t)  -- 'as' only meaningful for inl/inr/absurd

parseApp :: Parser Term
parseApp = foldl1 App <$> some parseAtom

parseAtom :: Parser Term
parseAtom
    =  (TmUnit <$ symbol "unit")
   <|> parsePairOrParens
   <|> (TmFst <$> (symbol "fst" *> parseAtom))
   <|> (TmSnd <$> (symbol "snd" *> parseAtom))
   <|> (TmInl <$> (symbol "inl" *> parseAtom) <*> pure TyUnit)  -- placeholder ty
   <|> (TmInr <$> (symbol "inr" *> parseAtom) <*> pure TyUnit)  -- placeholder ty
   <|> (TmAbsurd <$> (symbol "absurd" *> parseAtom) <*> pure TyUnit)  -- placeholder ty
   <|> (Var   <$> identifier)

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
