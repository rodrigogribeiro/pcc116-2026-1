module Untyped.Syntax.Named
  ( Term(..)
  ) where

data Term
  = Var String
  | Lam String Term
  | App Term Term
  deriving (Eq, Show)
