module CoC.Reduce
  ( whnf
  , nf
  , betaEq
  ) where

import CoC.Syntax.Term
import CoC.Subst (subst, alphaEq)

-- Reduce a term to weak-head normal form under the given context.
-- Delta-reduces defined variables; beta-reduces applications.
whnf :: Ctx -> Term -> Term
whnf ctx (Var x) =
  case lookupDef x ctx of
    Just t  -> whnf ctx t
    Nothing -> Var x
whnf ctx (App f a) =
  case whnf ctx f of
    Lam x _ body -> whnf ctx (subst x a body)
    f'           -> App f' a
whnf ctx (Ann t _) = whnf ctx t
whnf _   t         = t   -- Sort, Lam, Pi already in WHNF

-- Reduce a term to full normal form (normalises under binders).
nf :: Ctx -> Term -> Term
nf ctx t =
  case whnf ctx t of
    Sort k      -> Sort k
    Var x       -> Var x
    App f a     -> App (nf ctx f) (nf ctx a)
    Lam x ty b  ->
      let ctx' = extendCtx x ty ctx
      in  Lam x (nf ctx ty) (nf ctx' b)
    Pi  x ty b  ->
      let ctx' = extendCtx x ty ctx
      in  Pi  x (nf ctx ty) (nf ctx' b)
    Ann t' ty   -> Ann (nf ctx t') (nf ctx ty)

-- Definitional equality: two terms are beta-delta equal iff their
-- normal forms are alpha-equivalent.
betaEq :: Ctx -> Term -> Term -> Bool
betaEq ctx s t = alphaEq (nf ctx s) (nf ctx t)
