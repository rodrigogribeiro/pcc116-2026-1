module CoC.Syntax.Term
  ( Sort(..)
  , Term(..)
  , CtxEntry(..)
  , Ctx
  , entryType
  , lookupType
  , lookupDef
  , extendCtx
  , extendCtxDef
  ) where

-- The two sorts of the Calculus of Constructions.
data Sort
  = Star
  | Box
  deriving (Eq, Ord, Show)

data Term
  = Sort Sort
  | Var  String
  | App  Term Term
  | Lam  String Term Term
  | Pi   String Term Term
  | Ann  Term Term
  deriving (Eq, Show)

data CtxEntry
  = HasType Term
  | HasDef  Term Term
  deriving (Show)

type Ctx = [(String, CtxEntry)]

entryType :: CtxEntry -> Term
entryType (HasType a)   = a
entryType (HasDef  _ a) = a

lookupType :: String -> Ctx -> Maybe Term
lookupType x ctx = fmap entryType (lookup x ctx)

lookupDef :: String -> Ctx -> Maybe Term
lookupDef x ctx =
  case lookup x ctx of
    Just (HasDef t _) -> Just t
    _                 -> Nothing

extendCtx :: String -> Term -> Ctx -> Ctx
extendCtx x a ctx = (x, HasType a) : ctx

extendCtxDef :: String -> Term -> Term -> Ctx -> Ctx
extendCtxDef x t a ctx = (x, HasDef t a) : ctx
