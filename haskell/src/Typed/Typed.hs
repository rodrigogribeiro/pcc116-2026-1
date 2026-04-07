module Main where

import Control.Exception (SomeException, catch)
import System.IO
import Data.List (isPrefixOf)

import qualified Typed.Syntax.DeBruijn as DB
import qualified Typed.Parser.NamedParser as NP
import qualified Typed.Parser.DeBruijnParser as DBP
import qualified Typed.Parser.TypeParser as TP
import Typed.Typechecker (TyCtx, typecheck)
import Typed.Interpreter (EvalResult(..), eval)
import qualified Typed.Pretty.Named as PN
import qualified Typed.Pretty.DeBruijn as PDB
import Typed.Pretty.Type (renderTy)
import Typed.Tactic

-- Configuration

maxSteps :: Int
maxSteps = 1000000

-- REPL state

data TermMode = Named | DeBruijn

data ReplState
  = TermMode TermMode TyCtx   -- normal term evaluation mode
  | ProofMode ProofState       -- tactic proof construction mode

initialState :: ReplState
initialState = TermMode Named []

-- Input processing

processInput :: ReplState -> String -> IO ReplState
processInput st ":help"    = printHelp >> return st
processInput st ":quit"    = putStrLn "Goodbye." >> return st
processInput st ":q"       = putStrLn "Goodbye." >> return st
processInput st ""         = return st

-- Term mode command
processInput (TermMode _ ctx) ":mode named" =
  putStrLn "Switched to named mode." >> return (TermMode Named ctx)
processInput (TermMode _ ctx) ":mode db" =
  putStrLn "Switched to De Bruijn mode." >> return (TermMode DeBruijn ctx)
processInput st@(TermMode _ ctx) ":ctx" =
  printCtx ctx >> return st
processInput (TermMode m ctx) input
  | "proof " `isPrefixOf` input =
      let tyStr = drop 6 input
      in  case TP.parseTyFull tyStr of
            Left err -> do putStrLn $ "Parse error in type:\n" ++ show err
                           return (TermMode m ctx)
            Right ty -> do
              let ps = startProof ty
              putStrLn $ "Proving: " ++ renderTy ty
              putStrLn ""
              putStrLn (ppProofState ps)
              return (ProofMode ps)
  | otherwise =
      case m of
        Named    -> processNamed ctx input >> return (TermMode m ctx)
        DeBruijn -> processDeBruijn input  >> return (TermMode m ctx)
processInput (ProofMode _) ":abandon" = do
  putStrLn "Proof abandoned."
  return (TermMode Named [])
processInput (ProofMode ps) ":qed" =
  case finishProof ps of
    Left err -> do putStrLn $ "Cannot finish: " ++ err
                   return (ProofMode ps)
    Right t  -> do
      putStrLn "Proof complete!"
      putStrLn $ "  Term:  " ++ PN.renderTerm t
      case typecheck [] t of
        Left err -> putStrLn $ "  (type error: " ++ err ++ ")"
        Right ty -> putStrLn $ "  Type:  " ++ renderTy ty
      case DB.fromNamed [] t of
        Left err  -> putStrLn $ "  (scope error: " ++ err ++ ")"
        Right dbt -> do
          putStrLn $ "  DB:    " ++ PDB.renderTerm dbt
          case eval maxSteps dbt of
            Value v _ -> do
              let vn = DB.toNamed [] v
              putStrLn $ "  Value: " ++ PN.renderTerm vn
            StepLimit _ -> putStrLn "  (step limit reached)"
      return (TermMode Named [])
processInput (ProofMode ps) tacticStr =
  case runTactic tacticStr ps of
    Left err  -> do putStrLn $ "Tactic error: " ++ err
                    return (ProofMode ps)
    Right ps' -> do
      putStrLn (ppProofState ps')
      return (ProofMode ps')

-- Tactic dispatcher

runTactic :: String -> ProofState -> Either String ProofState
runTactic s ps =
  let ws = words s
  in case ws of
    ["intro", x]            -> introTactic x ps
    ["assumption"]          -> assumptionTactic ps
    ("exact" : rest)        -> case NP.parseFull (unwords rest) of
                                 Left err -> Left $ "parse error: " ++ show err
                                 Right t  -> exactTactic t ps
    ["apply", h]            -> applyTactic h ps
    ["split"]               -> splitTactic ps
    ["left"]                -> leftTactic ps
    ["right"]               -> rightTactic ps
    ["cases", h, x, y]      -> casesTactic h x y ps
    ["trivial"]             -> trivialTactic ps
    ["absurd", h]           -> absurdTactic h ps
    ["destruct", h, h1, h2] -> destructTactic h h1 h2 ps
    _ -> Left $ "Unknown tactic: " ++ s

-- Named mode

processNamed :: TyCtx -> String -> IO ()
processNamed ctx input =
  case NP.parseFull input of
    Left  err -> putStrLn $ "Parse error:\n" ++ show err
    Right nt  ->
      case typecheck ctx nt of
        Left  err -> putStrLn $ "Type error: " ++ err
        Right ty  ->
          case DB.fromNamed [] nt of
            Left  err -> putStrLn $ "Scope error: " ++ err
            Right dbt -> do
              putStrLn $ "  Type:      " ++ renderTy ty
              putStrLn $ "  Named:     " ++ PN.renderTerm nt
              putStrLn $ "  De Bruijn: " ++ PDB.renderTerm dbt
              evalAndPrint dbt

-- De Bruijn mode

processDeBruijn :: String -> IO ()
processDeBruijn input =
  case DBP.parseFull input of
    Left  err -> putStrLn $ "Parse error:\n" ++ show err
    Right dbt -> do
      let nt = DB.toNamed [] dbt
      putStrLn $ "  De Bruijn: " ++ PDB.renderTerm dbt
      putStrLn $ "  Named:     " ++ PN.renderTerm nt
      evalAndPrint dbt

-- Evaluation helper

evalAndPrint :: DB.Term -> IO ()
evalAndPrint dbt =
  case eval maxSteps dbt of
    Value result n -> do
      let nt = DB.toNamed [] result
      putStrLn $ "  Value (" ++ show n ++ " step"
               ++ (if n == 1 then "" else "s") ++ "):"
      putStrLn $ "    Named:     " ++ PN.renderTerm nt
      putStrLn $ "    De Bruijn: " ++ PDB.renderTerm result
    StepLimit result -> do
      let nt = DB.toNamed [] result
      putStrLn $ "  Step limit (" ++ show maxSteps ++ ") reached."
      putStrLn $ "  Last term:"
      putStrLn $ "    Named:     " ++ PN.renderTerm nt
      putStrLn $ "    De Bruijn: " ++ PDB.renderTerm result

printCtx :: TyCtx -> IO ()
printCtx [] = putStrLn "  (empty context)"
printCtx ctx = mapM_ (\(x, ty) -> putStrLn $ "  " ++ x ++ " : " ++ renderTy ty) ctx

-- REPL loop

repl :: ReplState -> IO ()
repl st = do
  putStr (prompt st)
  hFlush stdout
  eof <- isEOF
  if eof
    then putStrLn "\nGoodbye."
    else do
      line <- getLine
      let input = strip line
      case input of
        ":quit" -> putStrLn "Goodbye."
        ":q"    -> putStrLn "Goodbye."
        _       -> do
          st' <- processInput st input
                   `catch` handler st
          repl st'
  where
    handler :: ReplState -> SomeException -> IO ReplState
    handler st' ex = putStrLn ("Error: " ++ show ex) >> return st'

prompt :: ReplState -> String
prompt (TermMode Named    _)  = "ch-named> "
prompt (TermMode DeBruijn _)  = "ch-db> "
prompt (ProofMode ps) =
  let n = length (goals ps)
  in  "tactic(" ++ show n ++ ")> "

strip :: String -> String
strip = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

-- Help

printHelp :: IO ()
printHelp = mapM_ putStrLn
  [ ""
  , "=== Curry-Howard STLC REPL ==="
  , ""
  , "Term mode commands:"
  , "  :mode named        switch to named term input"
  , "  :mode db           switch to De Bruijn input"
  , "  :ctx               show the current typing context"
  , "  proof τ            enter tactic proof mode for proposition τ"
  , "  :help              show this help"
  , "  :quit / :q         exit"
  , ""
  , "Types / Propositions:"
  , "  ⊤  (or Top)        Truth / unit type"
  , "  ⊥  (or Bot)        Falsehood / void type"
  , "  A → B              Implication / function type (right-assoc)"
  , "  A × B  (or A * B)  Conjunction / product type (left-assoc)"
  , "  A + B              Disjunction / sum type (left-assoc)"
  , "  P, Q, R, ...       Propositional variables (uppercase)"
  , ""
  , "Term syntax (named):"
  , "  unit               proof of ⊤"
  , "  (t, u)             proof of A ∧ B"
  , "  fst t              proof of A from t : A ∧ B"
  , "  snd t              proof of B from t : A ∧ B"
  , "  inl t as A+B       left injection (proof of A ∨ B)"
  , "  inr t as A+B       right injection"
  , "  case t of (inl x => t1 | inr y => t2)"
  , "  absurd t as τ      ex falso (t : ⊥)"
  , "  \\x:A. t            proof of A → B"
  , "  t u                modus ponens / application"
  , ""
  , "Tactic proof mode  (enter with 'proof τ'):"
  , "  intro x            introduce implication hypothesis as x"
  , "  assumption         close goal by matching hypothesis"
  , "  exact t            close goal with explicit proof term t"
  , "  apply h            apply hypothesis h to the current goal"
  , "  split              split conjunction goal into two subgoals"
  , "  left               prove left side of disjunction"
  , "  right              prove right side of disjunction"
  , "  cases h x y        case-split on h : A ∨ B (bind payloads as x, y)"
  , "  trivial            close ⊤ goal"
  , "  absurd h           close any goal using h : ⊥"
  , "  destruct h h1 h2   split h : A ∧ B into h1 : A and h2 : B"
  , "  :qed               finish proof (when no goals remain)"
  , "  :abandon           abandon the current proof"
  , ""
  , "Examples:"
  , "  -- term mode:"
  , "  (\\x:P. x)"
  , "  (\\x:P*Q. fst x)"
  , "  inl unit as Top+P"
  , ""
  , "  -- tactic mode:"
  , "  proof P -> P"
  , "    intro h"
  , "    assumption"
  , "    :qed"
  , ""
  , "  proof (P -> Q) -> (Q -> R) -> P -> R"
  , "    intro hpq"
  , "    intro hqr"
  , "    intro hp"
  , "    apply hqr"
  , "    apply hpq"
  , "    assumption"
  , "    :qed"
  , ""
  ]

-- Entry point

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  putStrLn "Propositional Logic REPL"
  putStrLn "Type :help for usage, :quit to exit"
  repl initialState
