module Typed.Pretty.Type
  ( prettyTy
  , renderTy
  , addParens
  ) where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

import Typed.Syntax.Type

-- Pretty printer

prettyTy :: Ty -> Doc ann
prettyTy = prettyTyPrec 0

prettyTyPrec :: Int -> Ty -> Doc ann
prettyTyPrec p (TyArr a b) =
  addParens (p > 0) $
    prettyTyPrec 1 a <+> pretty "→" <+> prettyTyPrec 0 b
prettyTyPrec p (TySum a b) =
  addParens (p > 1) $
    prettyTyPrec 1 a <+> pretty "+" <+> prettyTyPrec 2 b
prettyTyPrec p (TyProd a b) =
  addParens (p > 2) $
    prettyTyPrec 2 a <+> pretty "×" <+> prettyTyPrec 3 b
prettyTyPrec _ TyUnit      = pretty "⊤"
prettyTyPrec _ TyVoid      = pretty "⊥"
prettyTyPrec _ (TyVar v)   = pretty v

renderTy :: Ty -> String
renderTy = renderString . layoutPretty defaultLayoutOptions . prettyTy

addParens :: Bool -> Doc ann -> Doc ann
addParens True  d = lparen <> d <> rparen
addParens False d = d
