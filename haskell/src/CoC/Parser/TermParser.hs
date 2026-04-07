module CoC.Parser.TermParser
  ( parseTerm
  , parseFull
  ) where

import Data.Void
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import CoC.Syntax.Term

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
reservedWords = ["let", "in"]

identifier :: Parser String
identifier = lexeme $ try $ do
  c  <- letterChar <|> char '_'
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reservedWords
    then fail $ "reserved word: " ++ name
    else return name

-- Grammar
--
-- expr   ::= lam | namedPi | arrow
-- lam    ::= ('λ'|'\') binder+ '.' expr
-- namedPi::= ('Π'|'∀') binder+ '.' expr
-- arrow  ::= app ('->'|'→') expr | app
-- app    ::= atom+
-- atom   ::= '*' | '□' | ident | '(' expr ')' | '(' expr ':' expr ')'
-- binder ::= '(' ident ':' expr ')'

parseTerm :: Parser Term
parseTerm = sc *> parseExpr

parseExpr :: Parser Term
parseExpr = parseLam <|> parseNamedPi <|> parseArrow

parseLam :: Parser Term
parseLam = do
  void $ lexeme (char '\\' <|> char 'λ')
  bs <- some parseBinder
  void $ symbol "."
  body <- parseExpr
  return $ foldr (\(x, ty) t -> Lam x ty t) body bs

parseNamedPi :: Parser Term
parseNamedPi = do
  void $ lexeme (char 'Π' <|> char '∀')
  bs <- some parseBinder
  void $ symbol "."
  body <- parseExpr
  return $ foldr (\(x, ty) t -> Pi x ty t) body bs

-- A → B (right-associative anonymous Pi)
parseArrow :: Parser Term
parseArrow = do
  lhs <- parseApp
  option lhs $ do
    void $ symbol "->" <|> symbol "→"
    rhs <- parseExpr
    return (Pi "_" lhs rhs)

parseApp :: Parser Term
parseApp = foldl1 App <$> some parseAtom

parseAtom :: Parser Term
parseAtom
  =  (Sort Star <$ (symbol "*"  <|> symbol "★"))
 <|> (Sort Box  <$ (symbol "□"  <|> symbol "Box"))
 <|> parseParens
 <|> (Var <$> identifier)

-- '(' expr ')' or '(' expr ':' expr ')'
parseParens :: Parser Term
parseParens = between (symbol "(") (symbol ")") $ do
  t <- parseExpr
  option t $ do
    void $ symbol ":"
    ty <- parseExpr
    return (Ann t ty)

parseBinder :: Parser (String, Term)
parseBinder = between (symbol "(") (symbol ")") $ do
  x  <- identifier
  void $ symbol ":"
  ty <- parseExpr
  return (x, ty)

parseFull :: String -> Either (ParseErrorBundle String Void) Term
parseFull input = parse (parseTerm <* eof) "<input>" input
