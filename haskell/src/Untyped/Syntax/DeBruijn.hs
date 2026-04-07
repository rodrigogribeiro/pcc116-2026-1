module Untyped.Syntax.DeBruijn
  ( Term(..)
  , Context
  , fromNamed
  , toNamed
  ) where

import qualified Untyped.Syntax.Named as N
import Data.List (findIndex)

-- De Bruijn index representation of untyped lambda calculus.
data Term
  = Var Int
  | Lam Term
  | App Term Term
  deriving (Eq, Show)

type Context = [String]

fromNamed :: Context -> N.Term -> Either String Term
fromNamed ctx (N.Var x) =
  case findIndex (== x) ctx of
    Just i  -> Right (Var i)
    Nothing -> Left $ "Unbound variable: " ++ x
fromNamed ctx (N.Lam x body) =
  Lam <$> fromNamed (x : ctx) body
fromNamed ctx (N.App t1 t2) =
  App <$> fromNamed ctx t1 <*> fromNamed ctx t2

toNamed :: Context -> Term -> N.Term
toNamed ctx (Var i)
  | i < length ctx = N.Var (ctx !! i)
  | otherwise      = N.Var ("_" ++ show i)
toNamed ctx (Lam body) =
  let name = freshName ctx
  in  N.Lam name (toNamed (name : ctx) body)
toNamed ctx (App t1 t2) =
  N.App (toNamed ctx t1) (toNamed ctx t2)

freshName :: Context -> String
freshName ctx =
  case filter (`notElem` ctx) candidates of
    (n : _) -> n
    []      -> error "freshName: exhausted names (impossible)"
  where
    candidates = [ c : suffix
                 | suffix <- "" : map show [(1 :: Int) ..]
                 , c      <- ['a' .. 'z']
                 ]
