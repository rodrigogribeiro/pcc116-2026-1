module CoC.Subst
  ( freeVars
  , freshFor
  , subst
  , alphaEq
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import CoC.Syntax.Term

-- Free variables of a term.
freeVars :: Term -> Set String
freeVars (Sort _)      = Set.empty
freeVars (Var x)       = Set.singleton x
freeVars (App f a)     = freeVars f `Set.union` freeVars a
freeVars (Ann t ty)    = freeVars t `Set.union` freeVars ty
freeVars (Lam x a b)   = freeVars a `Set.union` Set.delete x (freeVars b)
freeVars (Pi  x a b)   = freeVars a `Set.union` Set.delete x (freeVars b)

-- Generate a fresh name not in the given set.
-- Appends primes until the name is not in the set.
freshFor :: Set String -> String -> String
freshFor used x
  | x `Set.notMember` used = x
  | otherwise               = freshFor used (x ++ "'")

-- Capture-avoiding substitution: @subst x s t@ computes @t[x := s]@.
subst :: String -> Term -> Term -> Term
subst x s t = go t
  where
    fvs = freeVars s

    go (Sort k)    = Sort k
    go (Var y)     | y == x    = s
                   | otherwise = Var y
    go (App f a)   = App (go f) (go a)
    go (Ann u ty)  = Ann (go u) (go ty)
    go (Lam y a b)
      | y == x         = Lam y (go a) b          -- x is shadowed
      | y `Set.member` fvs =
          let y' = freshFor (fvs `Set.union` freeVars b `Set.union` Set.singleton x) y
              b' = subst y (Var y') b
          in  Lam y' (go a) (go b')
      | otherwise      = Lam y (go a) (go b)
    go (Pi y a b)
      | y == x         = Pi y (go a) b
      | y `Set.member` fvs =
          let y' = freshFor (fvs `Set.union` freeVars b `Set.union` Set.singleton x) y
              b' = subst y (Var y') b
          in  Pi y' (go a) (go b')
      | otherwise      = Pi y (go a) (go b)

-- Alpha-equivalence: two terms are alpha-equal if they differ only in
-- the names of bound variables. We check this by a simultaneous traversal
-- that maintains a bijection between bound-variable names.
alphaEq :: Term -> Term -> Bool
alphaEq = go [] []
  where
    -- env1, env2: stacks of (name, depth) pairs for each side
    go _  _  (Sort k1)     (Sort k2)     = k1 == k2
    go e1 e2 (Var x)       (Var y)       =
      case (lookup x e1, lookup y e2) of
        (Just d1, Just d2) -> d1 == d2          -- both bound: same depth
        (Nothing, Nothing) -> x == y            -- both free: same name
        _                  -> False
    go e1 e2 (App f1 a1)   (App f2 a2)   = go e1 e2 f1 f2 && go e1 e2 a1 a2
    go e1 e2 (Ann t1 ty1)  (Ann t2 ty2)  = go e1 e2 t1 t2 && go e1 e2 ty1 ty2
    go e1 e2 (Lam x a1 b1) (Lam y a2 b2) =
      let d = length e1
      in  go e1 e2 a1 a2 && go ((x,d):e1) ((y,d):e2) b1 b2
    go e1 e2 (Pi x a1 b1)  (Pi y a2 b2)  =
      let d = length e1
      in  go e1 e2 a1 a2 && go ((x,d):e1) ((y,d):e2) b1 b2
    go _  _  _              _             = False
