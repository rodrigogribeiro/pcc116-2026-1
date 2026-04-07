{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Typed.Tactic
  ( Goal(..)
  , ProofState(..)
  , startProof
  , finishProof
  , ppGoal
  , ppProofState
  -- Tactics
  , introTactic
  , assumptionTactic
  , exactTactic
  , applyTactic
  , splitTactic
  , leftTactic
  , rightTactic
  , casesTactic
  , trivialTactic
  , absurdTactic
  , destructTactic
  ) where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

import Typed.Syntax.Type
import qualified Typed.Syntax.Named as N
import Typed.Pretty.Type (renderTy, prettyTy)
import Typed.Typechecker (typecheck)

-- Proof state

-- A single proof goal: hypotheses in scope and the type to prove.
data Goal = Goal
  { hyps   :: [(String, Ty)]   -- local hypotheses (name, type)
  , goalTy :: Ty               -- the type we must inhabit
  } deriving (Show)

-- An assembler takes one proof term per open goal and produces the full term.
type Assembler = [N.Term] -> N.Term

data ProofState = ProofState
  { goals    :: [Goal]
  , assemble :: Assembler
  }

-- Start a proof of type ty with empty hypotheses.
startProof :: Ty -> ProofState
startProof ty = ProofState
  { goals    = [Goal { hyps = [], goalTy = ty }]
  , assemble = \ts -> case ts of { [t] -> t; _ -> error "startProof: impossible" }
  }

-- Extract the completed proof term (only succeeds when there are no open goals).
finishProof :: ProofState -> Either String N.Term
finishProof ps
  | null (goals ps) = Right (assemble ps [])
  | otherwise       = Left $ show (length (goals ps)) ++ " goal(s) remaining"

-- Pretty-printing goals

ppGoal :: Goal -> String
ppGoal g = renderString . layoutPretty defaultLayoutOptions $ doc
  where
    doc = vcat (map ppHyp (reverse (hyps g)))
          <> line <> pretty (replicate 40 '-')
          <> line <> prettyTy (goalTy g)
    ppHyp (x, ty) = pretty x <+> pretty ":" <+> prettyTy ty

ppProofState :: ProofState -> String
ppProofState ps
  | null (goals ps) = "No goals. Use :qed to finish."
  | otherwise =
      let n = length (goals ps)
          header = show n ++ " goal" ++ (if n == 1 then "" else "s") ++ ":"
          gStr   = case goals ps of { (g:_) -> ppGoal g; [] -> "" }
          rest   = if n > 1
                   then "\n(+ " ++ show (n - 1) ++ " more goal"
                        ++ (if n - 1 == 1 then "" else "s") ++ ")"
                   else ""
      in  header ++ "\n" ++ gStr ++ rest

-- Tactic combinator

-- Apply a goal-refining function to the first open goal.
refine :: (Goal -> Either String ([Goal], [N.Term] -> N.Term)) -> ProofState -> Either String ProofState
refine _ (ProofState [] _) = Left "No goals to prove."
refine f (ProofState (g:gs) asm) =
  case f g of
    Left err -> Left err
    Right (newGoals, combinator) ->
      Right $ ProofState
        { goals    = newGoals ++ gs
        , assemble = \ts ->
            let n            = length newGoals
                (here, rest) = splitAt n ts
            in  asm (combinator here : rest)
        }

-- Tactics

-- intro x: introduce hypothesis x for goal A → B.
introTactic :: String -> ProofState -> Either String ProofState
introTactic x = refine $ \g ->
  case goalTy g of
    TyArr a b ->
      let newGoal = g { hyps = (x, a) : hyps g, goalTy = b }
      in  Right ([newGoal], \[t] -> N.Lam x a t)
    _ -> Left $ "intro: goal is not an implication, it is " ++ renderTy (goalTy g)

-- Close the goal by finding a matching hypothesis.
assumptionTactic :: ProofState -> Either String ProofState
assumptionTactic = refine $ \g ->
  case filter ((== goalTy g) . snd) (hyps g) of
    ((x, _) : _) -> Right ([], \[] -> N.Var x)
    []            -> Left "assumption: no hypothesis matches the goal"

-- Close the goal with an explicit proof term (must type-check against goal).
exactTactic :: N.Term -> ProofState -> Either String ProofState
exactTactic t = refine $ \g ->
  case typecheck (hyps g) t of
    Left err -> Left $ "exact: " ++ err
    Right ty ->
      if ty == goalTy g
        then Right ([], \[] -> t)
        else Left $ "exact: term has type " ++ renderTy ty
                 ++ " but goal is " ++ renderTy (goalTy g)

-- apply h: apply hypothesis h : A1 -> ... -> An -> B to goal B,
-- opening subgoals A1, ..., An.
applyTactic :: String -> ProofState -> Either String ProofState
applyTactic hName = refine $ \g ->
  case lookup hName (hyps g) of
    Nothing -> Left $ "apply: " ++ hName ++ " not in context"
    Just ty ->
      let (argTys, retTy) = unfoldArr ty
      in  if retTy == goalTy g
          then
            let newGoals   = map (\a -> g { goalTy = a }) argTys
                combinator ts = foldl N.App (N.Var hName) ts
            in  Right (newGoals, combinator)
          else Left $ "apply: conclusion of " ++ hName
                   ++ " is " ++ renderTy retTy
                   ++ " but goal is " ++ renderTy (goalTy g)
  where
    unfoldArr (TyArr a b) = let (as_, r) = unfoldArr b in (a : as_, r)
    unfoldArr t           = ([], t)

-- split: prove a conjunction A & B by opening goals A and B.
splitTactic :: ProofState -> Either String ProofState
splitTactic = refine $ \g ->
  case goalTy g of
    TyProd a b ->
      Right ( [g { goalTy = a }, g { goalTy = b }]
            , \[t1, t2] -> N.TmPair t1 t2 )
    _ -> Left $ "split: goal is not a conjunction, it is " ++ renderTy (goalTy g)

-- left: prove a disjunction A || B via the left branch.
leftTactic :: ProofState -> Either String ProofState
leftTactic = refine $ \g ->
  case goalTy g of
    TySum a b ->
      Right ( [g { goalTy = a }]
            , \[t] -> N.TmInl t (TySum a b) )
    _ -> Left $ "left: goal is not a disjunction, it is " ++ renderTy (goalTy g)

-- right: prove a disjunction A || B via the right branch.
rightTactic :: ProofState -> Either String ProofState
rightTactic = refine $ \g ->
  case goalTy g of
    TySum a b ->
      Right ( [g { goalTy = b }]
            , \[t] -> N.TmInr t (TySum a b) )
    _ -> Left $ "right: goal is not a disjunction, it is " ++ renderTy (goalTy g)

-- trivial: prove True.
trivialTactic :: ProofState -> Either String ProofState
trivialTactic = refine $ \g ->
  case goalTy g of
    TyUnit -> Right ([], \[] -> N.TmUnit)
    _      -> Left $ "trivial: goal is not ⊤, it is " ++ renderTy (goalTy g)

-- absurd h: close any goal given a proof of False in the context.
absurdTactic :: String -> ProofState -> Either String ProofState
absurdTactic hName = refine $ \g ->
  case lookup hName (hyps g) of
    Nothing      -> Left $ "absurd: " ++ hName ++ " not in context"
    Just TyVoid  -> Right ([], \[] -> N.TmAbsurd (N.Var hName) (goalTy g))
    Just ty      -> Left $ "absurd: " ++ hName ++ " has type " ++ renderTy ty
                         ++ ", expected ⊥"

-- cases h x y: case-split on disjunctive hypothesis h : A || B,
-- binding the left payload as x and the right payload as y.
casesTactic :: String -> String -> String -> ProofState -> Either String ProofState
casesTactic hName x y = refine $ \g ->
  case lookup hName (hyps g) of
    Nothing -> Left $ "cases: " ++ hName ++ " not in context"
    Just ty ->
      case ty of
        TySum a b ->
          let g1 = g { hyps = (x, a) : hyps g }
              g2 = g { hyps = (y, b) : hyps g }
              combinator [t1, t2] = N.TmCase (N.Var hName) x t1 y t2
              combinator _        = error "casesTactic: impossible"
          in  Right ([g1, g2], combinator)
        _ -> Left $ "cases: " ++ hName ++ " has type " ++ renderTy ty
                 ++ ", expected a sum type"

-- destruct h h1 h2: split product hypothesis h : A & B into h1 : A and h2 : B.
destructTactic :: String -> String -> String -> ProofState -> Either String ProofState
destructTactic hName h1 h2 = refine $ \g ->
  case lookup hName (hyps g) of
    Nothing -> Left $ "destruct: " ++ hName ++ " not in context"
    Just ty ->
      case ty of
        TyProd a b ->
          let newHyps = (h1, a) : (h2, b) : filter ((/= hName) . fst) (hyps g)
              newGoal = g { hyps = newHyps }
              -- Introduce h1 = fst h, h2 = snd h via let-style application
              combinator [t] =
                N.App (N.App (N.Lam h1 a (N.Lam h2 b t))
                             (N.TmFst (N.Var hName)))
                             (N.TmSnd (N.Var hName))
              combinator _ = error "destructTactic: impossible"
          in  Right ([newGoal], combinator)
        _ -> Left $ "destruct: " ++ hName ++ " has type " ++ renderTy ty
                 ++ ", expected a product type"
