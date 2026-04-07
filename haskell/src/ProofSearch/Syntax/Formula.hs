module ProofSearch.Syntax.Formula
  ( Formula (..),
    Sequent (..),
    RuleName (..),
    ProofTree (..),
  )
where

import Data.List (intercalate)

-- Propositional formulas

data Formula
  = Atom String
  | Top
  | Bot
  | And Formula Formula
  | Or Formula Formula
  | Imp Formula Formula
  deriving (Eq, Ord)

instance Show Formula where
  show (Atom p) = p
  show Top = "⊤"
  show Bot = "⊥"
  show (And a b) = "(" ++ show a ++ " ∧ " ++ show b ++ ")"
  show (Or a b) = "(" ++ show a ++ " ∨ " ++ show b ++ ")"
  show (Imp a b) = "(" ++ show a ++ " → " ++ show b ++ ")"

-- Sequent  Γ ⊢ G

data Sequent = Sequent
  { antecedent :: [Formula],
    succedent :: Formula
  }
  deriving (Eq)

instance Show Sequent where
  show (Sequent [] g) = "⊢ " ++ show g
  show (Sequent fs g) = intercalate ", " (map show fs) ++ " ⊢ " ++ show g

-- Calculus rule names  (Dyckhoff 1992)

data RuleName
  = Ax -- axiom:  P ∈ Γ, G = P  (P atomic)
  | TopR -- ⊤-R:    Γ ⊢ ⊤
  | BotL -- ⊥-L:    ⊥ ∈ Γ
  | ImpR -- →-R:    Γ, A ⊢ B  /  Γ ⊢ A → B
  | AndR -- ∧-R:    Γ ⊢ A  Γ ⊢ B  /  Γ ⊢ A ∧ B
  | AndL -- ∧-L:    Γ, A, B ⊢ G  /  Γ, A ∧ B ⊢ G
  | OrL -- ∨-L:    Γ, A ⊢ G  Γ, B ⊢ G  /  Γ, A ∨ B ⊢ G
  | OrR1 -- ∨-R₁:   Γ ⊢ A  /  Γ ⊢ A ∨ B
  | OrR2 -- ∨-R₂:   Γ ⊢ B  /  Γ ⊢ A ∨ B
  | ImpLAtom -- L1: P ∈ Γ, P→Q ∈ Γ  →  replace P→Q by Q
  | ImpLTop -- L4: ⊤→C ∈ Γ  →  replace by C
  | ImpLBot -- ⊥→C ∈ Γ  →  drop it (trivially true)
  | ImpLAnd -- L2: (A∧B)→C ∈ Γ  →  replace by A→B→C
  | ImpLOr -- L3: (A∨B)→C ∈ Γ  →  replace by A→C, B→C
  | ImpLImp -- L5: (A→B)→C ∈ Γ  →  two premises
  deriving (Eq, Show)

-- Proof tree

data ProofTree = ProofTree
  { ptRule :: RuleName,
    ptConclusion :: Sequent,
    ptPremises :: [ProofTree]
  }
  deriving (Show)
