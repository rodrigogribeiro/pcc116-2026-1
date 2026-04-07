{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module CoC.Tactic
  ( Goal(..)
  , ProofState(..)
  , startProof
  , finishProof
  , ppGoal
  , ppProofState
  -- Tactics
  , introTactic
  , introTypeTactic
  , applyTactic
  , exactTactic
  , assumptionTactic
  , splitTactic
  , leftTactic
  , rightTactic
  , existsTactic
  , unfoldTactic
  , trivialTactic
  , absurdTactic
  ) where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

import CoC.Syntax.Term
import CoC.Subst (subst)
import CoC.Reduce (whnf, betaEq)
import CoC.Check (infer)
import CoC.Encode (topTy, botTy)
import CoC.Pretty.Term (prettyTerm, renderTerm)

-- A single proof goal: the local context and the type to inhabit.
data Goal = Goal
  { cocCtx  :: Ctx     -- local context (hypotheses + definitions)
  , goalTy  :: Term    -- the CoC type we must provide a term for
  } deriving (Show)

type Assembler = [Term] -> Term

data ProofState = ProofState
  { goals    :: [Goal]
  , assemble :: Assembler
  , history  :: [String]   -- tactic strings applied so far (for :save)
  }

startProof :: Ctx -> Term -> ProofState
startProof ctx ty = ProofState
  { goals    = [Goal { cocCtx = ctx, goalTy = ty }]
  , assemble = \ts -> case ts of { [t] -> t; _ -> error "startProof: impossible" }
  , history  = []
  }

finishProof :: ProofState -> Either String Term
finishProof ps
  | null (goals ps) = Right (assemble ps [])
  | otherwise       = Left $ show (length (goals ps)) ++ " goal(s) remaining"

-- Pretty-printing

ppGoal :: Goal -> String
ppGoal g = renderString . layoutPretty defaultLayoutOptions $ doc
  where
    doc = vcat (map ppEntry (reverse (cocCtx g)))
          <> line <> pretty (replicate 40 '-')
          <> line <> prettyTerm (goalTy g)
    ppEntry (x, HasType ty)  = pretty x <+> pretty ":" <+> prettyTerm ty
    ppEntry (x, HasDef t ty) = pretty x <+> pretty ":=" <+> prettyTerm t
                             <+> pretty ":" <+> prettyTerm ty

ppProofState :: ProofState -> String
ppProofState ps
  | null (goals ps) = "No goals. Use :qed to finish."
  | otherwise =
      let n      = length (goals ps)
          header = show n ++ " goal" ++ (if n == 1 then "" else "s") ++ ":"
          gStr   = case goals ps of { (g:_) -> ppGoal g; [] -> "" }
          rest   = if n > 1
                   then "\n(+ " ++ show (n-1) ++ " more goal"
                        ++ (if n-1 == 1 then "" else "s") ++ ")"
                   else ""
      in  header ++ "\n" ++ gStr ++ rest

-- Core combinator

refine :: (Goal -> Either String ([Goal], [Term] -> Term))
       -> ProofState -> Either String ProofState
refine _ (ProofState [] _ _)  = Left "No goals to prove."
refine f (ProofState (g:gs) asm hist) =
  case f g of
    Left err -> Left err
    Right (newGoals, combinator) ->
      Right $ ProofState
        { goals    = newGoals ++ gs
        , assemble = \ts ->
            let n            = length newGoals
                (here, rest) = splitAt n ts
            in  asm (combinator here : rest)
        , history  = hist
        }

-- Tactics

-- intro x: introduce the outermost Π/→ binder as hypothesis x.
introTactic :: String -> ProofState -> Either String ProofState
introTactic x = refine $ \g ->
  case whnf (cocCtx g) (goalTy g) of
    Pi binder dom cod ->
      let cod'    = subst binder (Var x) cod
          ctx'    = extendCtx x dom (cocCtx g)
          newGoal = g { cocCtx = ctx', goalTy = cod' }
      in  Right ([newGoal], \[t] -> Lam x dom t)
    other -> Left $ "intro: goal is not a Π-type, got: " ++ renderTerm other

-- introType x: introduce a type-level Π binder (domain is *).
introTypeTactic :: String -> ProofState -> Either String ProofState
introTypeTactic x = refine $ \g ->
  case whnf (cocCtx g) (goalTy g) of
    Pi binder (Sort Star) cod ->
      let cod'    = subst binder (Var x) cod
          ctx'    = extendCtx x (Sort Star) (cocCtx g)
          newGoal = g { cocCtx = ctx', goalTy = cod' }
      in  Right ([newGoal], \[t] -> Lam x (Sort Star) t)
    Pi _ dom _ ->
      Left $ "introType: binder domain is not *, it is: " ++ renderTerm dom
    other ->
      Left $ "introType: goal is not a Π-type, got: " ++ renderTerm other

-- apply h: apply h (a function in the context) to the current goal,
-- generating subgoals for each argument.
applyTactic :: String -> ProofState -> Either String ProofState
applyTactic hName = refine $ \g ->
  case lookupType hName (cocCtx g) of
    Nothing -> Left $ "apply: " ++ hName ++ " not in context"
    Just hTy ->
      let (argTys, retTy) = unfoldPi (cocCtx g) hTy
      in  if betaEq (cocCtx g) retTy (goalTy g)
          then
            let newGoals   = map (\a -> g { goalTy = a }) argTys
                combinator ts = foldl App (Var hName) ts
            in  Right (newGoals, combinator)
          else Left $ "apply: conclusion of " ++ hName
                   ++ " is " ++ renderTerm retTy
                   ++ " but goal is " ++ renderTerm (goalTy g)

-- Unfold Pi-type spine, returning (argument types, return type).
unfoldPi :: Ctx -> Term -> ([Term], Term)
unfoldPi ctx ty =
  case whnf ctx ty of
    Pi x dom cod ->
      let (args, ret) = unfoldPi (extendCtx x dom ctx) cod
      in  (dom : args, ret)
    other -> ([], other)

-- exact t: close the goal with a parsed/provided term.
exactTactic :: Term -> ProofState -> Either String ProofState
exactTactic t = refine $ \g ->
  case infer (cocCtx g) t of
    Left err -> Left $ "exact: " ++ err
    Right ty ->
      if betaEq (cocCtx g) ty (goalTy g)
        then Right ([], \[] -> t)
        else Left $ "exact: term has type " ++ renderTerm ty
                 ++ " but goal is " ++ renderTerm (goalTy g)

-- assumption: close the goal by finding a matching hypothesis.
assumptionTactic :: ProofState -> Either String ProofState
assumptionTactic = refine $ \g ->
  case filter (betaEq (cocCtx g) (goalTy g) . entryType . snd) (cocCtx g) of
    ((x, _) : _) -> Right ([], \[] -> Var x)
    []            -> Left "assumption: no hypothesis matches the goal"

-- split: prove A ∧ B (Church-encoded) — opens subgoals for A and B.
-- Recognises the shape Πc:*. (A → B → c) → c
splitTactic :: ProofState -> Either String ProofState
splitTactic = refine $ \g ->
  case matchAnd (cocCtx g) (goalTy g) of
    Nothing      -> Left $ "split: goal does not look like A ∧ B, got: "
                         ++ renderTerm (goalTy g)
    Just (a, b)  ->
      let goalA = g { goalTy = a }
          goalB = g { goalTy = b }
          -- proof: λc:*. λf:A→B→c. f ha hb
          combinator [ha, hb] =
            Lam "c" (Sort Star)
              (Lam "f" (Pi "_" a (Pi "_" b (Var "c")))
                (App (App (Var "f") ha) hb))
          combinator _ = error "splitTactic: impossible"
      in  Right ([goalA, goalB], combinator)

matchAnd :: Ctx -> Term -> Maybe (Term, Term)
matchAnd ctx ty =
  case whnf ctx ty of
    Pi c (Sort Star) body | c == "c" || True ->
      case whnf ctx body of
        Pi _ (Pi _ a (Pi _ b ret)) ret2
          | betaEq ctx ret (Var "c") && betaEq ctx ret2 (Var "c") ->
              Just (a, b)
        _ -> Nothing
    _ -> Nothing

-- left: prove A ∨ B via left injection.
-- Shape: Πc:*. (A→c) → (B→c) → c
leftTactic :: ProofState -> Either String ProofState
leftTactic = refine $ \g ->
  case matchOr (cocCtx g) (goalTy g) of
    Nothing     -> Left $ "left: goal does not look like A ∨ B, got: "
                        ++ renderTerm (goalTy g)
    Just (a, b) ->
      -- proof: λc:*. λfl:A→c. λfr:B→c. fl ha
      let combinator [ha] =
            Lam "c" (Sort Star)
              (Lam "fl" (Pi "_" a (Var "c"))
                (Lam "fr" (Pi "_" b (Var "c"))
                  (App (Var "fl") ha)))
          combinator _ = error "leftTactic: impossible"
      in  Right ([g { goalTy = a }], combinator)

-- right: prove A ∨ B via right injection.
rightTactic :: ProofState -> Either String ProofState
rightTactic = refine $ \g ->
  case matchOr (cocCtx g) (goalTy g) of
    Nothing     -> Left $ "right: goal does not look like A ∨ B, got: "
                        ++ renderTerm (goalTy g)
    Just (a, b) ->
      let combinator [hb] =
            Lam "c" (Sort Star)
              (Lam "fl" (Pi "_" a (Var "c"))
                (Lam "fr" (Pi "_" b (Var "c"))
                  (App (Var "fr") hb)))
          combinator _ = error "rightTactic: impossible"
      in  Right ([g { goalTy = b }], combinator)

matchOr :: Ctx -> Term -> Maybe (Term, Term)
matchOr ctx ty =
  case whnf ctx ty of
    Pi _ (Sort Star) body ->
      case whnf ctx body of
        Pi _ (Pi _ a _) rest ->
          case whnf ctx rest of
            Pi _ (Pi _ b _) _ -> Just (a, b)
            _                  -> Nothing
        _ -> Nothing
    _ -> Nothing

-- exists t: prove ∃x:A.B by providing the witness t.
-- Shape: Πc:*. (Πx:A. B→c) → c
existsTactic :: Term -> ProofState -> Either String ProofState
existsTactic witness = refine $ \g ->
  case matchExists (cocCtx g) (goalTy g) of
    Nothing          -> Left $ "exists: goal does not look like ∃x:A.B, got: "
                             ++ renderTerm (goalTy g)
    Just (x, a, b)   ->
      let bWit    = subst x witness b
          combinator [hb] =
            Lam "c" (Sort Star)
              (Lam "k" (Pi x a (Pi "_" b (Var "c")))
                (App (App (Var "k") witness) hb))
          combinator _ = error "existsTactic: impossible"
      in  Right ([g { goalTy = bWit }], combinator)

matchExists :: Ctx -> Term -> Maybe (String, Term, Term)
matchExists ctx ty =
  case whnf ctx ty of
    Pi _ (Sort Star) body ->
      case whnf ctx body of
        Pi _ (Pi x a (Pi _ b _)) _ -> Just (x, a, b)
        _                           -> Nothing
    _ -> Nothing

-- unfold name: replace the definition of name in the goal type.
unfoldTactic :: String -> ProofState -> Either String ProofState
unfoldTactic name = refine $ \g ->
  case lookup name (cocCtx g) of
    Just (HasDef defn _) ->
      let newTy = subst name defn (goalTy g)
      in  Right ([g { goalTy = newTy }], \[t] -> t)
    Just (HasType _) ->
      Left $ "unfold: " ++ name ++ " has no definition (use :def to define it)"
    Nothing ->
      Left $ "unfold: " ++ name ++ " not in context"

-- trivial: prove ⊤ (= Πα:*. α→α).
trivialTactic :: ProofState -> Either String ProofState
trivialTactic = refine $ \g ->
  if betaEq (cocCtx g) (goalTy g) topTy
    then Right ([], \[] -> Lam "a" (Sort Star) (Lam "x" (Var "a") (Var "x")))
    else Left $ "trivial: goal is not ⊤, got: " ++ renderTerm (goalTy g)

-- absurd h: close any goal given h : ⊥ (= Πα:*. α) in context.
absurdTactic :: String -> ProofState -> Either String ProofState
absurdTactic hName = refine $ \g ->
  case lookupType hName (cocCtx g) of
    Nothing -> Left $ "absurd: " ++ hName ++ " not in context"
    Just hTy ->
      if betaEq (cocCtx g) hTy botTy
        then
          -- proof: h goalTy
          Right ([], \[] -> App (Var hName) (goalTy g))
        else Left $ "absurd: " ++ hName ++ " has type " ++ renderTerm hTy
                 ++ ", expected ⊥"
