module Typed.Syntax.DeBruijn
  ( Term(..)
  , NameCtx
  , fromNamed
  , toNamed
  ) where

import Data.List (findIndex)
import Typed.Syntax.Type
import qualified Typed.Syntax.Named as N

-- De Bruijn proof terms.
data Term
  = Var     Int
  | Lam     Ty   Term
  | App     Term Term
  | TmUnit
  | TmPair  Term Term
  | TmFst   Term
  | TmSnd   Term
  | TmInl   Term Ty
  | TmInr   Term Ty
  | TmCase  Term Term Term   -- scrutinee, left-branch (binds 0), right-branch (binds 0)
  | TmAbsurd Term Ty
  deriving (Eq, Show)

type NameCtx = [String]

-- Named -> De Bruijn

fromNamed :: NameCtx -> N.Term -> Either String Term
fromNamed ctx (N.Var x)
  = case findIndex (== x) ctx of
    Just i  -> Right (Var i)
    Nothing -> Left $ "Unbound variable: " ++ x
fromNamed ctx (N.Lam x ty body)
  = Lam ty <$> fromNamed (x : ctx) body
fromNamed ctx (N.App t1 t2)
  = App <$> fromNamed ctx t1 <*> fromNamed ctx t2
fromNamed _   N.TmUnit
  = Right TmUnit
fromNamed ctx (N.TmPair t1 t2)
  = TmPair <$> fromNamed ctx t1 <*> fromNamed ctx t2
fromNamed ctx (N.TmFst t)
  = TmFst  <$> fromNamed ctx t
fromNamed ctx (N.TmSnd t)
  = TmSnd  <$> fromNamed ctx t
fromNamed ctx (N.TmInl t ty)
  = TmInl  <$> fromNamed ctx t <*> pure ty
fromNamed ctx (N.TmInr t ty)
  = TmInr  <$> fromNamed ctx t <*> pure ty
fromNamed ctx (N.TmCase t x t1 y t2)
  = TmCase <$> fromNamed ctx t
           <*> fromNamed (x : ctx) t1
           <*> fromNamed (y : ctx) t2
fromNamed ctx (N.TmAbsurd t ty)
  = TmAbsurd <$> fromNamed ctx t <*> pure ty

-- De Bruijn -> Named

toNamed :: NameCtx -> Term -> N.Term
toNamed ctx (Var i)
  | i < length ctx = N.Var (ctx !! i)
  | otherwise      = N.Var ("_" ++ show i)
toNamed ctx (Lam ty body)
  = let name = freshName ctx
    in  N.Lam name ty (toNamed (name : ctx) body)
toNamed ctx (App t1 t2)
  = N.App    (toNamed ctx t1) (toNamed ctx t2)
toNamed _   TmUnit
  = N.TmUnit
toNamed ctx (TmPair t1 t2)
  = N.TmPair (toNamed ctx t1) (toNamed ctx t2)
toNamed ctx (TmFst t)
  = N.TmFst  (toNamed ctx t)
toNamed ctx (TmSnd t)
  = N.TmSnd  (toNamed ctx t)
toNamed ctx (TmInl t ty)
  = N.TmInl  (toNamed ctx t) ty
toNamed ctx (TmInr t ty)
  = N.TmInr  (toNamed ctx t) ty
toNamed ctx (TmCase t t1 t2)
  = let x = freshName ctx
        y = freshName (x : ctx)
    in  N.TmCase (toNamed ctx t)
                 x
                 (toNamed (x : ctx) t1)
                 y
                 (toNamed (y : ctx) t2)
toNamed ctx (TmAbsurd t ty)
  = N.TmAbsurd (toNamed ctx t) ty

-- Generate a fresh variable name not in the context.
freshName :: NameCtx -> String
freshName ctx =
  case filter (`notElem` ctx) candidates of
    (n : _) -> n
    []      -> error "freshName: impossible"
  where
    candidates = [ c : suffix
                 | suffix <- "" : map show [(1 :: Int) ..]
                 , c      <- ['a' .. 'z']
                 ]
