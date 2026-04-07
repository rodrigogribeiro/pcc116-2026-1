module Typed.Syntax.Type
  ( Ty(..)
  ) where

data Ty
  = TyVar String
  | TyUnit
  | TyVoid
  | TyArr Ty Ty
  | TyProd Ty Ty
  | TySum Ty Ty
  deriving (Eq, Show)
