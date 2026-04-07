module CoC.Check
  ( infer
  , check
  , inferSort
  ) where

import CoC.Syntax.Term
import CoC.Subst (subst)
import CoC.Reduce (whnf, betaEq)

-- Valid (s1, s2) pairs for the Pi-formation rule in lambda-C (full CoC).
validRule :: Sort -> Sort -> Bool
validRule _ _ = True

-- Infer the type of a term in the given context.
infer :: Ctx -> Term -> Either String Term
infer _   (Sort Star)   = Right (Sort Box)
infer _   (Sort Box)    = Left "□ has no type in the Calculus of Constructions"
infer ctx (Var x)       =
  case lookupType x ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Variable not in scope: " ++ x
infer ctx (Ann t ty)    = do
  _ <- inferSort ctx ty
  check ctx t ty
  return ty
infer ctx (App f a)     = do
  fTy <- infer ctx f
  case whnf ctx fTy of
    Pi x dom cod -> do
      check ctx a dom
      return (subst x a cod)
    other -> Left $ "Expected a function type, got: " ++ show other
infer ctx (Lam x a body) = do
  _ <- inferSort ctx a
  let ctx' = extendCtx x a ctx
  b <- infer ctx' body
  return (Pi x a b)
infer ctx (Pi x a b)    = do
  s1 <- inferSort ctx a
  let ctx' = extendCtx x a ctx
  s2 <- inferSort ctx' b
  if validRule s1 s2
    then return (Sort s2)
    else Left $ "Invalid PTS rule: (" ++ show s1 ++ ", " ++ show s2 ++ ")"

-- Check that a term has a given type (up to definitional equality).
check :: Ctx -> Term -> Term -> Either String ()
check ctx t expected = do
  actual <- infer ctx t
  if betaEq ctx actual expected
    then Right ()
    else Left $ "Type mismatch:\n  expected: " ++ show (whnf ctx expected)
             ++ "\n  actual:   " ++ show (whnf ctx actual)

-- Infer the sort (*  or □) of a type expression.
inferSort :: Ctx -> Term -> Either String Sort
inferSort ctx ty = do
  k <- infer ctx ty
  case whnf ctx k of
    Sort s -> Right s
    other  -> Left $ "Expected a sort, got: " ++ show other
