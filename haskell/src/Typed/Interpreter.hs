module Typed.Interpreter
  ( shift
  , subst
  , betaReduce
  , isValue
  , step
  , EvalResult(..)
  , eval
  ) where

import Typed.Syntax.DeBruijn

-- Shifting and substitution

shift :: Int -> Int -> Term -> Term
shift d c (Var k)
  | k >= c    = Var (k + d)
  | otherwise = Var k
shift d c (Lam ty body)
  = Lam ty (shift d (c + 1) body)
shift d c (App t1 t2)
  = App (shift d c t1) (shift d c t2)
shift _  _ TmUnit
  = TmUnit
shift d c (TmPair t1 t2)
  = TmPair (shift d c t1) (shift d c t2)
shift d c (TmFst t)
  = TmFst (shift d c t)
shift d c (TmSnd t)
  = TmSnd (shift d c t)
shift d c (TmInl t ty)
  = TmInl (shift d c t) ty
shift d c (TmInr t ty)
  = TmInr (shift d c t) ty
shift d c (TmCase t t1 t2)
  = TmCase (shift d c t)
           (shift d (c + 1) t1)
           (shift d (c + 1) t2)
shift d c (TmAbsurd t ty)
  = TmAbsurd (shift d c t) ty

subst :: Int -> Term -> Term -> Term
subst j s (Var k)
  | k == j = s
  | otherwise = Var k
subst j s (Lam ty body)
  = Lam ty (subst (j + 1) (shift 1 0 s) body)
subst j s (App t1 t2)
  = App (subst j s t1) (subst j s t2)
subst _  _ TmUnit
  = TmUnit
subst j s (TmPair t1 t2)
  = TmPair (subst j s t1) (subst j s t2)
subst j s (TmFst t)
  = TmFst (subst j s t)
subst j s (TmSnd t)
  = TmSnd (subst j s t)
subst j s (TmInl t ty)
  = TmInl (subst j s t) ty
subst j s (TmInr t ty)
  = TmInr (subst j s t) ty
subst j s (TmCase t t1 t2)
  = TmCase (subst j s t)
           (subst (j + 1) (shift 1 0 s) t1)
           (subst (j + 1) (shift 1 0 s) t2)
subst j s (TmAbsurd t ty)
  = TmAbsurd (subst j s t) ty

-- Beta-reduce: substitute argument into lambda body.
betaReduce :: Term -> Term -> Term
betaReduce body arg
  = shift (-1) 0 (subst 0 (shift 1 0 arg) body)

-- Call-by-value small-step reduction

isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue TmUnit = True
isValue (TmPair v1 v2) = isValue v1 && isValue v2
isValue (TmInl v _) = isValue v
isValue (TmInr v _) = isValue v
isValue _ = False

-- One call-by-value step.  Returns Nothing when the term is a value (or stuck).
step :: Term -> Maybe Term
step (App (Lam _ body) v)
  | isValue v = Just (betaReduce body v)
step (App t1 t2)
  | not (isValue t1) = flip App t2 <$> step t1
step (App t1 t2) = App t1 <$> step t2
step (TmFst (TmPair v1 _))
  | isValue v1 = Just v1
step (TmSnd (TmPair _ v2))
  | isValue v2 = Just v2
step (TmFst t) = TmFst <$> step t
step (TmSnd t) = TmSnd <$> step t
step (TmPair t1 t2)
  | not (isValue t1) = flip TmPair t2 <$> step t1
step (TmPair t1 t2) = TmPair t1 <$> step t2
step (TmInl t ty)
  | not (isValue t) = flip TmInl ty <$> step t
step (TmInr t ty)
  | not (isValue t) = flip TmInr ty <$> step t
step (TmCase (TmInl v _) t1 _)
  | isValue v = Just (betaReduce t1 v)
step (TmCase (TmInr v _) _ t2)
  | isValue v = Just (betaReduce t2 v)
step (TmCase t t1 t2)
  = (\t' -> TmCase t' t1 t2) <$> step t
step (TmAbsurd t ty) = flip TmAbsurd ty <$> step t
step _ = Nothing

-- Evaluation with step limit

data EvalResult
  = Value     Term Int  -- Reached a value; Int is steps taken.
  | StepLimit Term      -- Hit the step limit.
  deriving (Show)

eval :: Int -> Term -> EvalResult
eval maxSteps = go 0
  where
    go n t
      | n >= maxSteps = StepLimit t
      | otherwise     =
          case step t of
            Nothing -> Value t n
            Just t' -> go (n + 1) t'
