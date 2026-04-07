module ProofSearch.Pretty.ProofTree
  ( prettyFormula,
    prettySequent,
    renderFormula,
    renderSequent,
    renderProofTree,
    describeRule,
  )
where

import Prettyprinter
import Prettyprinter.Render.String (renderString)
import ProofSearch.Syntax.Formula

-- Formula pretty-printer

prettyFormula :: Formula -> Doc ann
prettyFormula = ppF 0

ppF :: Int -> Formula -> Doc ann
ppF _ (Atom p) = pretty p
ppF _ Top = pretty "⊤"
ppF _ Bot = pretty "⊥"
ppF p (Imp a b) =
  addParens (p > 0) $ ppF 1 a <+> pretty "→" <+> ppF 0 b
ppF p (Or a b) =
  addParens (p > 1) $ ppF 1 a <+> pretty "∨" <+> ppF 2 b
ppF p (And a b) =
  addParens (p > 2) $ ppF 2 a <+> pretty "∧" <+> ppF 3 b

addParens :: Bool -> Doc ann -> Doc ann
addParens True d = lparen <> d <> rparen
addParens False d = d

-- Sequent pretty-printer

prettySequent :: Sequent -> Doc ann
prettySequent (Sequent [] g) =
  pretty "⊢" <+> prettyFormula g
prettySequent (Sequent fs g) =
  hsep (punctuate comma (map prettyFormula fs))
    <+> pretty "⊢"
    <+> prettyFormula g

-- Rule descriptions

describeRule :: RuleName -> String
describeRule Ax = "Ax"
describeRule TopR = "⊤-R"
describeRule BotL = "⊥-L"
describeRule ImpR = "→-R"
describeRule AndR = "∧-R"
describeRule AndL = "∧-L"
describeRule OrL = "∨-L"
describeRule OrR1 = "∨-R₁"
describeRule OrR2 = "∨-R₂"
describeRule ImpLAtom = "L1 (P→Q, P∈Γ)"
describeRule ImpLTop = "L4 (⊤→C)"
describeRule ImpLBot = "L0 (⊥→C, drop)"
describeRule ImpLAnd = "L2 ((A∧B)→C)"
describeRule ImpLOr = "L3 ((A∨B)→C)"
describeRule ImpLImp = "L5 ((A→B)→C)"

-- Proof tree renderer

renderProofTree :: ProofTree -> String
renderProofTree = unlines . drawTree

drawTree :: ProofTree -> [String]
drawTree (ProofTree rule conc prems) =
  let header =
        "["
          ++ describeRule rule
          ++ "] "
          ++ renderSequent conc
      subtrees = map drawTree prems
   in header : drawForest subtrees

drawForest :: [[String]] -> [String]
drawForest [] = []
drawForest [t] = shiftLast t
drawForest (t : ts) = shiftMid t ++ drawForest ts

shiftLast :: [String] -> [String]
shiftLast [] = []
shiftLast (l : ls) = ("└── " ++ l) : map ("    " ++) ls

shiftMid :: [String] -> [String]
shiftMid [] = []
shiftMid (l : ls) = ("├── " ++ l) : map ("│   " ++) ls

renderFormula :: Formula -> String
renderFormula = renderString . layoutPretty defaultLayoutOptions . prettyFormula

renderSequent :: Sequent -> String
renderSequent = renderString . layoutPretty defaultLayoutOptions . prettySequent
