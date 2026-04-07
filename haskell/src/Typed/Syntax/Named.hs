module Typed.Syntax.Named
  ( Term(..)
  ) where

import Typed.Syntax.Type

-- Named proof terms for the Curry-Howard STLC.
data Term
  = Var String
  | Lam String Ty Term
  | App Term Term
  | TmUnit
  | TmPair Term Term
  | TmFst Term
  | TmSnd Term
  | TmInl Term Ty
  | TmInr Term Ty
  | TmCase Term String Term String Term
  | TmAbsurd Term Ty
  deriving (Eq, Show)
