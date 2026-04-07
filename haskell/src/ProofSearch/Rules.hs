-- Contraction-free sequent calculi for intuitionistic logic.
--
-- Each function tries to apply one rule to a sequent.
-- Returns Nothing when the rule is not applicable, or
-- Just (ruleName, [subgoals]) when it fires.
module ProofSearch.Rules
  ( tryAx,
    tryTopR,
    tryBotL,
    tryImpR,
    tryAndR,
    tryAndL,
    tryOrL,
    tryOrR1,
    tryOrR2,
    tryImpLAtom,
    tryImpLTop,
    tryImpLBot,
    tryImpLAnd,
    tryImpLOr,
  )
where

import ProofSearch.Syntax.Formula

-- List utilities

removeAt :: Int -> [a] -> [a]
removeAt i xs = take i xs ++ drop (i + 1) xs

replaceAt :: Int -> a -> [a] -> [a]
replaceAt i x xs = take i xs ++ [x] ++ drop (i + 1) xs

replaceAtWith :: Int -> [a] -> [a] -> [a]
replaceAtWith i new xs = take i xs ++ new ++ drop (i + 1) xs

-- Axiom and structural rules

tryAx :: Sequent -> Maybe (RuleName, [Sequent])
tryAx (Sequent gamma g@(Atom _))
  | g `elem` gamma = Just (Ax, [])
tryAx _ = Nothing

tryTopR :: Sequent -> Maybe (RuleName, [Sequent])
tryTopR (Sequent _ Top) = Just (TopR, [])
tryTopR _ = Nothing

tryBotL :: Sequent -> Maybe (RuleName, [Sequent])
tryBotL (Sequent gamma _)
  | Bot `elem` gamma = Just (BotL, [])
  | otherwise = Nothing

-- Right rules

tryImpR :: Sequent -> Maybe (RuleName, [Sequent])
tryImpR (Sequent gamma (Imp a b)) =
  Just (ImpR, [Sequent (a : gamma) b])
tryImpR _ = Nothing

tryAndR :: Sequent -> Maybe (RuleName, [Sequent])
tryAndR (Sequent gamma (And a b)) =
  Just (AndR, [Sequent gamma a, Sequent gamma b])
tryAndR _ = Nothing

tryOrR1 :: Sequent -> Maybe (RuleName, [Sequent])
tryOrR1 (Sequent gamma (Or a _)) = Just (OrR1, [Sequent gamma a])
tryOrR1 _ = Nothing

tryOrR2 :: Sequent -> Maybe (RuleName, [Sequent])
tryOrR2 (Sequent gamma (Or _ b)) = Just (OrR2, [Sequent gamma b])
tryOrR2 _ = Nothing

-- Left rules (invertible)

tryAndL :: Sequent -> Maybe (RuleName, [Sequent])
tryAndL (Sequent gamma g) =
  case [(a, b, i) | (i, And a b) <- zip [0 ..] gamma] of
    [] -> Nothing
    ((a, b, i) : _) ->
      let gamma' = replaceAtWith i [a, b] gamma
       in Just (AndL, [Sequent gamma' g])

tryOrL :: Sequent -> Maybe (RuleName, [Sequent])
tryOrL (Sequent gamma g) =
  case [(a, b, i) | (i, Or a b) <- zip [0 ..] gamma] of
    [] -> Nothing
    ((a, b, i) : _) ->
      let base = removeAt i gamma
       in Just (OrL, [Sequent (a : base) g, Sequent (b : base) g])

-- Left rules for implications  (Dyckhoff's L1, L4, L0, L2, L3)

tryImpLAtom :: Sequent -> Maybe (RuleName, [Sequent])
tryImpLAtom (Sequent gamma g) =
  case [(q, i) | (i, Imp p@(Atom _) q) <- zip [0 ..] gamma, p `elem` gamma] of
    [] -> Nothing
    ((q, i) : _) ->
      let gamma' = replaceAt i q gamma
       in Just (ImpLAtom, [Sequent gamma' g])

tryImpLTop :: Sequent -> Maybe (RuleName, [Sequent])
tryImpLTop (Sequent gamma g) =
  case [(c, i) | (i, Imp Top c) <- zip [0 ..] gamma] of
    [] -> Nothing
    ((c, i) : _) ->
      let gamma' = replaceAt i c gamma
       in Just (ImpLTop, [Sequent gamma' g])

tryImpLBot :: Sequent -> Maybe (RuleName, [Sequent])
tryImpLBot (Sequent gamma g) =
  case [i | (i, Imp Bot _) <- zip [0 ..] gamma] of
    [] -> Nothing
    (i : _) ->
      let gamma' = removeAt i gamma
       in Just (ImpLBot, [Sequent gamma' g])

tryImpLAnd :: Sequent -> Maybe (RuleName, [Sequent])
tryImpLAnd (Sequent gamma g) =
  case [(a, b, c, i) | (i, Imp (And a b) c) <- zip [0 ..] gamma] of
    [] -> Nothing
    ((a, b, c, i) : _) ->
      let gamma' = replaceAt i (Imp a (Imp b c)) gamma
       in Just (ImpLAnd, [Sequent gamma' g])

tryImpLOr :: Sequent -> Maybe (RuleName, [Sequent])
tryImpLOr (Sequent gamma g) =
  case [(a, b, c, i) | (i, Imp (Or a b) c) <- zip [0 ..] gamma] of
    [] -> Nothing
    ((a, b, c, i) : _) ->
      let gamma' = replaceAtWith i [Imp a c, Imp b c] gamma
       in Just (ImpLOr, [Sequent gamma' g])
