module Main where

import Control.Exception (SomeException, catch)
import System.IO

import qualified Untyped.Syntax.DeBruijn            as DB
import qualified Untyped.Parser.NamedParser          as NP
import qualified Untyped.Parser.DeBruijnParser       as DBP
import           Untyped.Interpreter                  (EvalResult(..), eval)
import qualified Untyped.Pretty.Named                as PN
import qualified Untyped.Pretty.DeBruijn             as PDB

-- Configuration

maxSteps :: Int
maxSteps = 1000000

-- REPL state

data Mode = Named | DeBruijn

data ReplState = ReplState { mode :: Mode }

initialState :: ReplState
initialState = ReplState { mode = Named }

-- Processing

processInput :: ReplState -> String -> IO ReplState
processInput st ":mode named" = do
  putStrLn "Switched to named mode."
  return st { mode = Named }
processInput st ":mode db" = do
  putStrLn "Switched to De Bruijn mode."
  return st { mode = DeBruijn }
processInput st ":help" = do
  printHelp
  return st
processInput st "" = return st
processInput st input =
  case mode st of
    Named    -> processNamed    input >> return st
    DeBruijn -> processDeBruijn input >> return st

processNamed :: String -> IO ()
processNamed input =
  case NP.parseFull input of
    Left  err -> putStrLn $ "Parse error:\n" ++ show err
    Right nt  ->
      case DB.fromNamed [] nt of
        Left  err -> putStrLn $ "Scope error: " ++ err
        Right dbt -> do
          putStrLn $ "  Input (named):    " ++ PN.renderTerm nt
          putStrLn $ "  Input (De Bruijn):" ++ " " ++ PDB.renderTerm dbt
          evalAndPrint dbt

processDeBruijn :: String -> IO ()
processDeBruijn input =
  case DBP.parseFull input of
    Left  err -> putStrLn $ "Parse error:\n" ++ show err
    Right dbt -> do
      let nt = DB.toNamed [] dbt
      putStrLn $ "  Input (De Bruijn):" ++ " " ++ PDB.renderTerm dbt
      putStrLn $ "  Input (named):    " ++ PN.renderTerm nt
      evalAndPrint dbt

evalAndPrint :: DB.Term -> IO ()
evalAndPrint dbt =
  case eval maxSteps dbt of
    NormalForm result n -> do
      let namedResult = DB.toNamed [] result
      putStrLn $ "  Normal form (" ++ show n ++ " step"
               ++ (if n == 1 then "" else "s") ++ "):"
      putStrLn $ "    Named:    " ++ PN.renderTerm namedResult
      putStrLn $ "    De Bruijn:" ++ " " ++ PDB.renderTerm result
    StepLimit result -> do
      let namedResult = DB.toNamed [] result
      putStrLn $ "  Step limit (" ++ show maxSteps ++ ") reached."
      putStrLn $ "  Last term:"
      putStrLn $ "    Named:    " ++ PN.renderTerm namedResult
      putStrLn $ "    De Bruijn:" ++ " " ++ PDB.renderTerm result

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
      case strip line of
        ":quit" -> putStrLn "Goodbye."
        ":q"    -> putStrLn "Goodbye."
        input   -> do
          st' <- processInput st input `catch` handler st
          repl st'
  where
    handler :: ReplState -> SomeException -> IO ReplState
    handler st' ex = do
      putStrLn $ "Error: " ++ show ex
      return st'

prompt :: ReplState -> String
prompt st = modeTag (mode st) ++ "> "
  where
    modeTag Named    = "named"
    modeTag DeBruijn = "db"

strip :: String -> String
strip = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

-- Help

printHelp :: IO ()
printHelp = mapM_ putStrLn
  [ ""
  , "Commands:"
  , "  :mode named   – switch to named term input mode"
  , "  :mode db      – switch to De Bruijn index input mode"
  , "  :help         – show this help"
  , "  :quit  / :q   – exit the REPL"
  , ""
  , "Syntax (named):"
  , "  Variables   : x, foo, x'"
  , "  Abstraction : \\x. t   or  λx. t   (multiple: \\x y z. t)"
  , "  Application : t1 t2 t3  (left-associative)"
  , "  Grouping    : (t)"
  , ""
  , "Syntax (De Bruijn):"
  , "  Variables   : 0, 1, 2, ..."
  , "  Abstraction : \\. t   or  λ. t"
  , "  Application : t1 t2 t3  (left-associative)"
  , "  Grouping    : (t)"
  , ""
  , "Examples (named):"
  , "  \\x. x                       – identity"
  , "  (\\x. x) (\\y. y)             – identity applied to identity"
  , "  \\f x. f (f x)               – Church numeral 2"
  , ""
  , "Examples (De Bruijn):"
  , "  \\. 0                        – identity"
  , "  (\\ . 0) (\\ . 0)             – identity applied to identity"
  , "  \\ . \\ . 1 (1 0)             – Church numeral 2"
  , ""
  ]

-- Entry point

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  putStrLn "Untyped Lambda Calculus REPL"
  putStrLn "Type :help for usage, :quit to exit"
  putStrLn $ "Reduction limit: " ++ show maxSteps ++ " steps."
  putStrLn "Default mode: named. Switch with :mode db / :mode named."
  repl initialState
