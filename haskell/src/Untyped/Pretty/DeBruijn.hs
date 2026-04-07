module Untyped.Pretty.DeBruijn
  ( prettyTerm
  , renderTerm
  ) where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

import Untyped.Syntax.DeBruijn

-- Pretty printer

prettyTerm :: Term -> Doc ann
prettyTerm = prettyPrec 0

prettyPrec :: Int -> Term -> Doc ann
prettyPrec _ (Var i) = pretty i
prettyPrec p (Lam body) =
  let
      (depth, b) = collectLams 1 body
      doc = pretty (replicate depth 'λ') <> pretty "." <+> prettyPrec 0 b
  in  addParens (p > 0) doc
prettyPrec p (App t1 t2) =
  let doc = prettyPrec 1 t1 <+> prettyPrec 2 t2
  in  addParens (p > 1) doc

collectLams :: Int -> Term -> (Int, Term)
collectLams n (Lam body) = collectLams (n + 1) body
collectLams n t          = (n, t)

addParens :: Bool -> Doc ann -> Doc ann
addParens True  d = lparen <> d <> rparen
addParens False d = d

-- Rendering

renderTerm :: Term -> String
renderTerm = renderString . layoutPretty defaultLayoutOptions . prettyTerm
