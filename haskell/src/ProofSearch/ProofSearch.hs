module Main where

import Control.Exception (SomeException, catch)
import ProofSearch.Syntax.Formula (ProofTree (..))
import ProofSearch.Parser.SequentParser (parseFull)
import ProofSearch.Pretty.ProofTree (renderProofTree, renderSequent)
import ProofSearch.Search (search)
import System.IO

-- REPL

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  putStrLn "Proof Search — Intuitionistic Propositional Logic"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "proof> "
  hFlush stdout
  eof <- isEOF
  if eof
    then putStrLn "\nGoodbye."
    else do
      line <- getLine
      let input = strip line
      case input of
        ":quit" -> putStrLn "Goodbye."
        ":q" -> putStrLn "Goodbye."
        ":help" -> printHelp >> repl
        "" -> repl
        _ -> (processInput input `catch` handler) >> repl
  where
    handler :: SomeException -> IO ()
    handler ex = putStrLn $ "Error: " ++ show ex

processInput :: String -> IO ()
processInput input =
  case parseFull input of
    Left err ->
      putStrLn $ "Parse error:\n" ++ show err
    Right seq_ -> do
      putStrLn $ "Searching for a proof of: " ++ renderSequent seq_
      putStrLn ""
      case search seq_ of
        Nothing ->
          putStrLn "✗  Not provable in intuitionistic propositional logic.\n"
        Just pt -> do
          putStrLn "✓  Proof found:\n"
          putStr (renderProofTree pt)
          putStrLn $
            "   ("
              ++ show (countSteps pt)
              ++ " rule application"
              ++ (if countSteps pt == 1 then "" else "s")
              ++ ")"
          putStrLn ""

countSteps :: ProofTree -> Int
countSteps (ProofTree _ _ []) = 1
countSteps (ProofTree _ _ prems) = 1 + sum (map countSteps prems)

strip :: String -> String
strip = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

-- Help message

printHelp :: IO ()
printHelp =
  mapM_
    putStrLn
    [ "",
      "=== Proof Search ===",
      "",
      "Enter a sequent to search for a proof.",
      "A sequent has the form:",
      "",
      "  Γ ⊢ G",
      "",
      "where Γ is a comma-separated list of formulas (the hypotheses)",
      "and G is the goal formula.",
      "",
      "Syntax:",
      "  Turnstile : |-  or  ⊢  or  =>",
      "  Implication  : A -> B  or  A → B   (right-associative)",
      "  Conjunction  : A /\\ B  or  A ∧ B   (left-associative)",
      "  Disjunction  : A \\/ B  or  A ∨ B   (left-associative)",
      "  Truth        : Top  or  ⊤",
      "  Falsehood    : Bot  or  ⊥",
      "  Atoms        : any identifier (P, Q, foo, x, …)",
      "  Grouping     : ( A )",
      "",
      "Examples:",
      "  |- P -> P",
      "  P -> Q, Q -> R |- P -> R",
      "  |- (P /\\ Q) -> (Q /\\ P)",
      "  |- (P -> Q -> R) -> (P -> Q) -> P -> R",
      "  |- (A \\/ B) -> (A -> C) -> (B -> C) -> C",
      "  P -> Q, P |- Q",
      "  |- (P -> Q -> P)",
      "  |- Bot -> P            -- ex falso",
      "  |- P \\/ (P -> Bot)    -- NOT provable (excluded middle)",
      "",
      "Rules used (Dyckhoff 1992):",
      "  Ax          axiom: G atomic, G ∈ Γ",
      "  ⊤-R         prove ⊤",
      "  ⊥-L         ⊥ in context",
      "  →-R         introduce implication",
      "  ∧-R         prove conjunction (two subgoals)",
      "  ∧-L         decompose conjunction in context",
      "  ∨-L         case-split on disjunction in context (two subgoals)",
      "  ∨-R₁/₂      prove disjunction via left/right branch",
      "  L1 (P→Q)    modus ponens when P is atomic and P ∈ Γ",
      "  L4 (⊤→C)    simplify ⊤→C to C",
      "  L0 (⊥→C)    drop ⊥→C (trivially true)",
      "  L2 ((A∧B)→C) curry: replace by A→B→C",
      "  L3 ((A∨B)→C) split: replace by A→C, B→C",
      "  L5 ((A→B)→C) the critical contraction-free rule",
      "",
      "Commands:",
      "  :help    show this help",
      "  :quit    exit",
      ""
    ]
