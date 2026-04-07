module Untyped.Interpreter
  ( shift
  , subst
  , betaReduce
  , step
  , EvalResult(..)
  , eval
  ) where

import Untyped.Syntax.DeBruijn

-- Substitution and shifting

shift :: Int -> Int -> Term -> Term
shift d c (Var k)
  | k >= c    = Var (k + d)
  | otherwise = Var k
shift d c (Lam body)
  = Lam (shift d (c + 1) body)
shift d c (App t1 t2)
  = App (shift d c t1) (shift d c t2)

subst :: Int -> Term -> Term -> Term
subst j s (Var k)
  | k == j    = s
  | otherwise = Var k
subst j s (Lam body)
  = Lam (subst (j + 1) (shift 1 0 s) body)
subst j s (App t1 t2)
  = App (subst j s t1) (subst j s t2)

betaReduce :: Term -> Term -> Term
betaReduce t1 t2
  = shift (-1) 0 (subst 0 (shift 1 0 t2) t1)

step :: Term -> Maybe Term
step (App (Lam body) t2)
  = Just (betaReduce body t2)
step (App t1 t2)
  = case step t1 of
    Just t1' -> Just (App t1' t2)
    Nothing  -> App t1 <$> step t2
step (Lam body)
  = Lam <$> step body
step _
  = Nothing

-- Evaluation with step limit

data EvalResult
  = NormalForm Term Int
  | StepLimit  Term
  deriving (Show)

eval :: Int -> Term -> EvalResult
eval maxSteps = go 0
  where
    go n t
      | n >= maxSteps = StepLimit t
      | otherwise     =
          case step t of
            Nothing -> NormalForm t n
            Just t' -> go (n + 1) t'
