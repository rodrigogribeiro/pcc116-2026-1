module Typed.Pretty.DeBruijn
  ( prettyTerm
  , renderTerm
  ) where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

import Typed.Syntax.DeBruijn
import Typed.Pretty.Type (prettyTy, addParens)

-- Pretty printer

prettyTerm :: Term -> Doc ann
prettyTerm = prettyPrec 0

prettyPrec :: Int -> Term -> Doc ann
prettyPrec _ (Var i)   = pretty i
prettyPrec _ TmUnit    = pretty "unit"
prettyPrec _ (TmPair t1 t2) =
  lparen <> prettyPrec 0 t1 <> comma <+> prettyPrec 0 t2 <> rparen
prettyPrec p (Lam ty body) =
  addParens (p > 0) $
    pretty "λ:" <> prettyTy ty <> pretty "." <+> prettyPrec 0 body
prettyPrec p (App t1 t2) =
  addParens (p > 1) $
    prettyPrec 1 t1 <+> prettyPrec 2 t2
prettyPrec p (TmFst t) =
  addParens (p > 1) $ pretty "fst" <+> prettyPrec 2 t
prettyPrec p (TmSnd t) =
  addParens (p > 1) $ pretty "snd" <+> prettyPrec 2 t
prettyPrec p (TmInl t ty) =
  addParens (p > 0) $
    pretty "inl" <+> prettyPrec 2 t <+> pretty "as" <+> prettyTy ty
prettyPrec p (TmInr t ty) =
  addParens (p > 0) $
    pretty "inr" <+> prettyPrec 2 t <+> pretty "as" <+> prettyTy ty
prettyPrec p (TmAbsurd t ty) =
  addParens (p > 0) $
    pretty "absurd" <+> prettyPrec 2 t <+> pretty "as" <+> prettyTy ty
prettyPrec p (TmCase t t1 t2) =
  addParens (p > 0) $
    pretty "case" <+> prettyPrec 1 t <+> pretty "of"
    <+> lparen
    <>  pretty "inl =>" <+> prettyPrec 0 t1
    <+> pretty "|"
    <+> pretty "inr =>" <+> prettyPrec 0 t2
    <>  rparen

-- Rendering

renderTerm :: Term -> String
renderTerm = renderString . layoutPretty defaultLayoutOptions . prettyTerm
