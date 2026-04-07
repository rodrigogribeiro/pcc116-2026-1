module ProofSearch.Parser.SequentParser
  ( parseFormula,
    parseSequent,
    parseFull,
  )
where

import Control.Monad (void)
import Data.Void
import ProofSearch.Syntax.Formula
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

sc :: Parser ()
sc =
  L.space
    space1
    (L.skipLineComment "--")
    (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parseFormula :: Parser Formula
parseFormula = do
  l <- parseOr
  option
    l
    ( do
        void $ symbol "->" <|> symbol "→"
        r <- parseFormula
        return (Imp l r)
    )

parseOr :: Parser Formula
parseOr = do
  t <- parseAnd
  ts <- many (orOp *> parseAnd)
  return $ foldl Or t ts
  where
    orOp = void (symbol "\\/") <|> void (symbol "∨")

parseAnd :: Parser Formula
parseAnd = do
  t <- parseAtom
  ts <- many (andOp *> parseAtom)
  return $ foldl And t ts
  where
    andOp = void (symbol "/\\") <|> void (symbol "∧") <|> void (symbol "&")

parseAtom :: Parser Formula
parseAtom =
  (Top <$ (symbol "Top" <|> symbol "⊤"))
    <|> (Bot <$ (symbol "Bot" <|> symbol "⊥"))
    <|> (Atom <$> ident)
    <|> between (symbol "(") (symbol ")") parseFormula

ident :: Parser String
ident = lexeme $ try $ do
  c <- letterChar
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reserved
    then fail $ "reserved word: " ++ name
    else return name
  where
    reserved = ["Top", "Bot"]

-- ---------------------------------------------------------------------------
-- Sequent grammar
--
-- Seq  ::= Ant '⊢' F  |  '⊢' F
-- Ant  ::= F (',' F)*
-- '⊢'  ::= '|-' | '⊢' | '=>'
-- ---------------------------------------------------------------------------

turnstile :: Parser ()
turnstile = void (symbol "|-") <|> void (symbol "⊢") <|> void (symbol "=>")

parseSequent :: Parser Sequent
parseSequent =
  sc
    *> (try withAntecedent <|> withoutAntecedent)
  where
    withAntecedent = do
      lhs <- parseFormula `sepBy1` symbol ","
      turnstile
      rhs <- parseFormula
      return (Sequent lhs rhs)

    withoutAntecedent = do
      turnstile
      rhs <- parseFormula
      return (Sequent [] rhs)

parseFull :: String -> Either (ParseErrorBundle String Void) Sequent
parseFull input = parse (parseSequent <* eof) "<input>" input
