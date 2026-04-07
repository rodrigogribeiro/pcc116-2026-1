module Main where

import Control.Exception (SomeException, catch)
import Data.List (isPrefixOf)
import System.IO

import CoC.Syntax.Term
import CoC.Check (infer)
import CoC.Reduce (nf, whnf)
import CoC.Encode (builtins)
import CoC.Parser.TermParser (parseFull)
import CoC.Pretty.Term (renderTerm)
import CoC.Tactic

-- REPL state

data ReplState
  = TermMode Ctx
  | ProofMode Ctx ProofState   -- global Ctx kept for :def during proof

initialState :: ReplState
initialState = TermMode builtinCtx

builtinCtx :: Ctx
builtinCtx = [ (name, HasDef def ty) | (name, def, ty) <- builtins ]

-- Process one line of input

processInput :: ReplState -> String -> IO ReplState

processInput st ""       = return st
processInput st ":help"  = printHelp >> return st
processInput st ":quit"  = putStrLn "Goodbye." >> return st
processInput st ":q"     = putStrLn "Goodbye." >> return st

-- Term-mode commands
processInput st@(TermMode ctx) ":ctx" = printCtx ctx >> return st

processInput (TermMode ctx) input
  | ":def " `isPrefixOf` input =
      processDef ctx (drop 5 input)
  | ":check " `isPrefixOf` input =
      processCheck ctx (drop 7 input) >> return (TermMode ctx)
  | ":eval " `isPrefixOf` input =
      processEval ctx (drop 6 input) >> return (TermMode ctx)
  | ":whnf " `isPrefixOf` input =
      processWhnf ctx (drop 6 input) >> return (TermMode ctx)
  | "proof " `isPrefixOf` input =
      startProofMode ctx (drop 6 input)
  | otherwise =
      processCheck ctx input >> return (TermMode ctx)

-- Proof-mode commands
processInput (ProofMode gctx _) ":abandon" = do
  putStrLn "Proof abandoned."
  return (TermMode gctx)

processInput (ProofMode gctx ps) ":qed" =
  case finishProof ps of
    Left err -> putStrLn ("Cannot finish: " ++ err) >> return (ProofMode gctx ps)
    Right t  -> do
      putStrLn "Proof complete!"
      putStrLn $ "  Term: " ++ renderTerm t
      case infer gctx t of
        Left err -> putStrLn $ "  (type error: " ++ err ++ ")"
        Right ty -> putStrLn $ "  Type: " ++ renderTerm ty
      return (TermMode gctx)

processInput (ProofMode gctx ps) input
  | ":save " `isPrefixOf` input = do
      let fname = drop 6 input
      writeFile fname (unlines (history ps))
      putStrLn $ "Proof script saved to " ++ fname
      return (ProofMode gctx ps)
  | otherwise =
      case runTactic input ps of
        Left err  -> putStrLn ("Tactic error: " ++ err) >> return (ProofMode gctx ps)
        Right ps' -> do
          let ps'' = ps' { history = history ps ++ [input] }
          putStrLn (ppProofState ps'')
          return (ProofMode gctx ps'')

-- Term-mode helpers

processDef :: Ctx -> String -> IO ReplState
processDef ctx s =
  case break (== ':') s of
    (nameRaw, ':':'=':rest) ->
      let name = strip nameRaw
      in  case parseFull (strip rest) of
            Left err -> do
              putStrLn $ "Parse error:\n" ++ show err
              return (TermMode ctx)
            Right t  ->
              case infer ctx t of
                Left err -> do
                  putStrLn $ "Type error: " ++ err
                  return (TermMode ctx)
                Right ty -> do
                  putStrLn $ name ++ " : " ++ renderTerm ty
                  let ctx' = extendCtxDef name t ty ctx
                  return (TermMode ctx')
    _ -> do
      putStrLn "Syntax: :def name := term"
      return (TermMode ctx)

processCheck :: Ctx -> String -> IO ()
processCheck ctx s =
  case parseFull s of
    Left err -> putStrLn $ "Parse error:\n" ++ show err
    Right t  ->
      case infer ctx t of
        Left err -> putStrLn $ "Type error: " ++ err
        Right ty -> putStrLn $ renderTerm t ++ " : " ++ renderTerm ty

processEval :: Ctx -> String -> IO ()
processEval ctx s =
  case parseFull s of
    Left err -> putStrLn $ "Parse error:\n" ++ show err
    Right t  ->
      case infer ctx t of
        Left err -> putStrLn $ "Type error: " ++ err
        Right ty -> do
          let v = nf ctx t
          putStrLn $ "  Value: " ++ renderTerm v
          putStrLn $ "  Type:  " ++ renderTerm ty

processWhnf :: Ctx -> String -> IO ()
processWhnf ctx s =
  case parseFull s of
    Left err -> putStrLn $ "Parse error:\n" ++ show err
    Right t  -> putStrLn $ renderTerm (whnf ctx t)

startProofMode :: Ctx -> String -> IO ReplState
startProofMode ctx s =
  case parseFull s of
    Left err -> do
      putStrLn $ "Parse error:\n" ++ show err
      return (TermMode ctx)
    Right ty -> do
      let ps = startProof ctx ty
      putStrLn $ "Proving: " ++ renderTerm ty
      putStrLn ""
      putStrLn (ppProofState ps)
      return (ProofMode ctx ps)

-- Tactic dispatcher

runTactic :: String -> ProofState -> Either String ProofState
runTactic s ps =
  case words s of
    ["intro",      x]   -> introTactic x ps
    ["introType",  x]   -> introTypeTactic x ps
    ["apply",      h]   -> applyTactic h ps
    ["assumption"]      -> assumptionTactic ps
    ["split"]           -> splitTactic ps
    ["left"]            -> leftTactic ps
    ["right"]           -> rightTactic ps
    ["trivial"]         -> trivialTactic ps
    ["absurd",     h]   -> absurdTactic h ps
    ["unfold",     n]   -> unfoldTactic n ps
    ("exact"    : rest) ->
      case parseFull (unwords rest) of
        Left err -> Left $ "parse error: " ++ show err
        Right t  -> exactTactic t ps
    ("exists"   : rest) ->
      case parseFull (unwords rest) of
        Left err -> Left $ "parse error: " ++ show err
        Right t  -> existsTactic t ps
    _ -> Left $ "Unknown tactic: " ++ s

-- Context display

printCtx :: Ctx -> IO ()
printCtx [] = putStrLn "  (empty context)"
printCtx ctx = mapM_ ppEntry (reverse ctx)
  where
    ppEntry (x, HasType ty)  = putStrLn $ "  " ++ x ++ " : " ++ renderTerm ty
    ppEntry (x, HasDef t ty) = putStrLn $ "  " ++ x ++ " := " ++ renderTerm t
                                        ++ " : " ++ renderTerm ty

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
prompt (TermMode _)      = "coc> "
prompt (ProofMode _ ps)  = "coc[" ++ show (length (goals ps)) ++ "]> "

strip :: String -> String
strip = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

-- Help

printHelp :: IO ()
printHelp = mapM_ putStrLn
  [ ""
  , "=== Calculus of Constructions REPL ==="
  , ""
  , "Term mode commands:"
  , "  :def x := t       define x as term t (added to context)"
  , "  :check t          infer and display the type of t"
  , "  :eval t           normalise t and show its value and type"
  , "  :whnf t           reduce t to weak-head normal form"
  , "  :ctx              show the current global context"
  , "  proof T           enter tactic proof mode for type T"
  , "  :help             show this help"
  , "  :quit / :q        exit"
  , ""
  , "Term syntax:"
  , "  *                 the sort of small types (Prop)"
  , "  □  or  Box        the sort of kinds"
  , "  x                 variable"
  , "  \\(x:A). t         lambda abstraction"
  , "  λ(x:A). t         lambda abstraction (unicode)"
  , "  Π(x:A). B         dependent product"
  , "  ∀(x:A). B         dependent product (unicode)"
  , "  A -> B            function type (anonymous Π)"
  , "  f a               application"
  , "  (t : A)           type annotation"
  , ""
  , "Built-in definitions:"
  , "  True              ⊤ = Πa:*. a → a"
  , "  False             ⊥ = Πa:*. a"
  , "  tt                proof of ⊤"
  , "  exFalso           ⊥ → Πa:*. a"
  , "  and_intro         Πa b:*. a → b → a ∧ b"
  , "  and_fst           Πa b:*. a ∧ b → a"
  , "  and_snd           Πa b:*. a ∧ b → b"
  , "  or_inl            Πa b:*. a → a ∨ b"
  , "  or_inr            Πa b:*. b → a ∨ b"
  , ""
  , "Tactic proof mode (enter with 'proof T'):"
  , "  intro x           introduce outermost Π/→ binder as x"
  , "  introType x       introduce type-level Π(x:*) binder as x"
  , "  apply h           apply h to goal, open subgoals for arguments"
  , "  exact t           close goal with explicit term t"
  , "  assumption        close goal by matching hypothesis"
  , "  split             prove A ∧ B: opens subgoals for A and B"
  , "  left              prove A ∨ B via left branch"
  , "  right             prove A ∨ B via right branch"
  , "  exists t          prove ∃x:A.B with witness t"
  , "  unfold name       unfold definition of name in goal"
  , "  trivial           prove ⊤"
  , "  absurd h          close any goal using h : ⊥"
  , "  :qed              finish proof when no goals remain"
  , "  :abandon          discard the current proof"
  , "  :save <file>      save tactic script to file"
  , ""
  , "Examples:"
  , "  -- Identity function:"
  , "  :def id := \\(a:*)(x:a). x"
  , ""
  , "  -- Tactic proof of P → P:"
  , "  proof \\(P:*). P -> P"
  , "    introType P"
  , "    intro h"
  , "    assumption"
  , "    :qed"
  , ""
  , "  -- Tactic proof of ∀A B: A ∧ B → A:"
  , "  proof ∀(a:*)∀(b:*). (∀(c:*).(a->b->c)->c) -> a"
  , "    introType a"
  , "    introType b"
  , "    intro h"
  , "    apply h"
  , "    intro ha"
  , "    intro hb"
  , "    assumption"
  , "    :qed"
  , ""
  ]

-- Entry point

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  putStrLn "Calculus of Constructions REPL"
  putStrLn "Type :help for usage, :quit to exit"
  putStrLn ""
  repl initialState
