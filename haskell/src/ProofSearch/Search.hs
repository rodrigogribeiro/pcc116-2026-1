--  Proof search (Dyckhoff 1992).
--
-- Strategy:
--   1. Apply deterministic invertible rules first (no backtracking needed).
--   2. Try non-invertible rules (∨-R₁/₂ and L5) with backtracking.
--
-- Termination is guaranteed by the weight of the multiset of formulas
-- strictly decreasing at each rule application (Dyckhoff 1992, Thm 4.2).
module ProofSearch.Search
  ( search,
  )
where

import Data.Maybe (maybeToList)
import ProofSearch.Syntax.Formula
import ProofSearch.Rules

-- Core search

-- Search for a proof of a sequent. Returns the first proof found,
-- or Nothing if the sequent is not provable.
search :: Sequent -> Maybe ProofTree
search s = firstSuccess (map (attempt s) (candidates s))

firstSuccess :: [Maybe a] -> Maybe a
firstSuccess [] = Nothing
firstSuccess (Just x : _) = Just x
firstSuccess (Nothing : xs) = firstSuccess xs

-- Apply a (rule, subgoals) pair and search all subgoals recursively.
attempt :: Sequent -> (RuleName, [Sequent]) -> Maybe ProofTree
attempt s (rn, subgoals) = do
  subproofs <- mapM search subgoals
  return $ ProofTree rn s subproofs

-- Candidate rule applications (ordered: invertible first)

-- All (rule, subgoals) pairs to try for a sequent, in priority order.
-- Invertible rules are listed first; non-invertible rules last.
candidates :: Sequent -> [(RuleName, [Sequent])]
candidates s =
  concat
    [ maybeToList (tryAx s),
      maybeToList (tryTopR s),
      maybeToList (tryBotL s),
      maybeToList (tryImpR s),
      maybeToList (tryAndR s),
      maybeToList (tryAndL s),
      maybeToList (tryOrL s),
      maybeToList (tryImpLBot s),
      maybeToList (tryImpLTop s),
      maybeToList (tryImpLAnd s),
      maybeToList (tryImpLOr s),
      maybeToList (tryImpLAtom s),
      maybeToList (tryOrR1 s),
      maybeToList (tryOrR2 s),
      impLImpCandidates s
    ]

impLImpCandidates :: Sequent -> [(RuleName, [Sequent])]
impLImpCandidates (Sequent gamma g) =
  [ (ImpLImp, [prem1, prem2])
  | (i, Imp (Imp a b) c) <- zip [0 ..] gamma,
    let base = removeAt i gamma
        prem1 = Sequent (Imp b c : base) (Imp a b)
        prem2 = Sequent (c : base) g
  ]
  where
    removeAt i xs = take i xs ++ drop (i + 1) xs
