module CoC.Pretty.Term
  ( prettyTerm
  , prettySort
  , renderTerm
  , renderSort
  , addParens
  ) where

import Data.Set (member)
import Prettyprinter
import Prettyprinter.Render.String (renderString)

import CoC.Syntax.Term
import CoC.Subst (freeVars)

addParens :: Bool -> Doc ann -> Doc ann
addParens True  d = lparen <> d <> rparen
addParens False d = d

prettySort :: Sort -> Doc ann
prettySort Star = pretty "*"
prettySort Box  = pretty "□"

prettyTerm :: Term -> Doc ann
prettyTerm = prettyPrec 0

prettyPrec :: Int -> Term -> Doc ann
prettyPrec _ (Sort s)   = prettySort s
prettyPrec _ (Var x)    = pretty x
prettyPrec p (Ann t ty) =
  addParens (p > 0) $
    prettyPrec 1 t <+> pretty ":" <+> prettyPrec 0 ty
prettyPrec p (App f a)  =
  addParens (p > 1) $
    prettyPrec 1 f <+> prettyPrec 2 a
prettyPrec p (Lam x ty body) =
  addParens (p > 0) $
    let (bs, b) = collectLam [(x, ty)] body
        ppB (v, t) = pretty v <> pretty ":" <> prettyPrec 2 t
    in  pretty "λ" <> hsep (map ppB bs) <> pretty "." <+> prettyPrec 0 b
prettyPrec p (Pi x ty body)
  | x == "_" || x `notMember` freeVars body =
      addParens (p > 0) $
        prettyPrec 1 ty <+> pretty "→" <+> prettyPrec 0 body
  | otherwise =
      addParens (p > 0) $
        let (bs, b) = collectPi [(x, ty)] body
            ppB (v, t) = pretty v <> pretty ":" <> prettyPrec 2 t
        in  pretty "Π" <> hsep (map ppB bs) <> pretty "." <+> prettyPrec 0 b
  where
    notMember k s = not (member k s)

collectLam :: [(String, Term)] -> Term -> ([(String, Term)], Term)
collectLam acc (Lam x ty b) = collectLam (acc ++ [(x, ty)]) b
collectLam acc t             = (acc, t)

collectPi :: [(String, Term)] -> Term -> ([(String, Term)], Term)
collectPi acc (Pi x ty b)
  | x /= "_" && x `elem` map fst acc' = (acc, Pi x ty b)
  | x /= "_"                           = collectPi (acc ++ [(x, ty)]) b
  where acc' = acc  -- avoid unused warning
collectPi acc t = (acc, t)

renderTerm :: Term -> String
renderTerm = renderString . layoutPretty defaultLayoutOptions . prettyTerm

renderSort :: Sort -> String
renderSort = renderString . layoutPretty defaultLayoutOptions . prettySort
