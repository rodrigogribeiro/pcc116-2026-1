module Untyped.Pretty.Named
  ( prettyTerm
  , renderTerm
  ) where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

import Untyped.Syntax.Named

-- Pretty printer

prettyTerm :: Term -> Doc ann
prettyTerm = prettyPrec 0

prettyPrec :: Int -> Term -> Doc ann
prettyPrec _ (Var x) = pretty x
prettyPrec p (Lam x body) =
  let (binders, b) = collectBinders [x] body
      doc = pretty "λ" <> hsep (map pretty binders) <> pretty "." <+> prettyPrec 0 b
  in  addParens (p > 0) doc
prettyPrec p (App t1 t2) =
  let doc = prettyPrec 1 t1 <+> prettyPrec 2 t2
  in  addParens (p > 1) doc

collectBinders :: [String] -> Term -> ([String], Term)
collectBinders xs (Lam x body) = collectBinders (xs ++ [x]) body
collectBinders xs t             = (xs, t)

addParens :: Bool -> Doc ann -> Doc ann
addParens True  d = lparen <> d <> rparen
addParens False d = d

renderTerm :: Term -> String
renderTerm = renderString . layoutPretty defaultLayoutOptions . prettyTerm
