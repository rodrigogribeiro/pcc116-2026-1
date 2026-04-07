module Typed.Typechecker
  ( TyCtx
  , typecheck
  ) where

import Typed.Syntax.Type
import qualified Typed.Syntax.Named as N
import Typed.Pretty.Type (renderTy)

-- Typing context: association list of variable names and their types.
type TyCtx = [(String, Ty)]

-- Infer the type of a named proof term under a context.
-- Returns the inferred type or a Left error message.
-- For inl/inr/absurd a correct 'as τ' annotation is required.
typecheck :: TyCtx -> N.Term -> Either String Ty
typecheck ctx (N.Var x) =
  case lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Unbound variable: " ++ x
typecheck ctx (N.Lam x ty body) = do
  bodyTy <- typecheck ((x, ty) : ctx) body
  return (TyArr ty bodyTy)
typecheck ctx (N.App t1 t2) = do
  ty1 <- typecheck ctx t1
  ty2 <- typecheck ctx t2
  case ty1 of
    TyArr argTy retTy ->
      if ty2 == argTy
        then Right retTy
        else Left $ "Type mismatch in application: expected "
                 ++ renderTy argTy ++ " but got " ++ renderTy ty2
    _ -> Left $ "Expected a function type, got " ++ renderTy ty1
typecheck _ N.TmUnit = Right TyUnit
typecheck ctx (N.TmPair t1 t2) = do
  ty1 <- typecheck ctx t1
  ty2 <- typecheck ctx t2
  return (TyProd ty1 ty2)
typecheck ctx (N.TmFst t) = do
  ty <- typecheck ctx t
  case ty of
    TyProd a _ -> Right a
    _ -> Left $ "fst: expected a product type, got " ++ renderTy ty
typecheck ctx (N.TmSnd t) = do
  ty <- typecheck ctx t
  case ty of
    TyProd _ b -> Right b
    _ -> Left $ "snd: expected a product type, got " ++ renderTy ty
typecheck ctx (N.TmInl t annot) =
  case annot of
    TySum a _ -> do
      ta <- typecheck ctx t
      if ta == a
        then Right annot
        else Left $ "inl: term has type " ++ renderTy ta
                 ++ " but annotation expects " ++ renderTy a
    TyUnit -> Left "inl: missing type annotation (write 'inl t as A + B')"
    _      -> Left $ "inl: annotation must be a sum type, got " ++ renderTy annot
typecheck ctx (N.TmInr t annot) =
  case annot of
    TySum _ b -> do
      tb <- typecheck ctx t
      if tb == b
        then Right annot
        else Left $ "inr: term has type " ++ renderTy tb
                 ++ " but annotation expects " ++ renderTy b
    TyUnit -> Left "inr: missing type annotation (write 'inr t as A + B')"
    _      -> Left $ "inr: annotation must be a sum type, got " ++ renderTy annot
typecheck ctx (N.TmCase t x t1 y t2) = do
  tty <- typecheck ctx t
  case tty of
    TySum a b -> do
      ty1 <- typecheck ((x, a) : ctx) t1
      ty2 <- typecheck ((y, b) : ctx) t2
      if ty1 == ty2
        then Right ty1
        else Left $ "case branches have different types: "
                 ++ renderTy ty1 ++ " vs " ++ renderTy ty2
    _ -> Left $ "case: scrutinee must have a sum type, got " ++ renderTy tty
typecheck ctx (N.TmAbsurd t annot) = do
  ty <- typecheck ctx t
  case ty of
    TyVoid -> case annot of
      TyUnit -> Left "absurd: missing type annotation (write 'absurd t as τ')"
      _      -> Right annot
    _ -> Left $ "absurd: term must have type ⊥, got " ++ renderTy ty
