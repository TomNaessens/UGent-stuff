-- -- --| Project: Functionele en Logische Programmeertalen
-- -- --| Deel: Haskell
-- -- --| Auteur: Tom Naessens
-- -- --| File: Main
-- -- --|       Reads input from a file, parses it to an AST,
-- -- --|       executes the live coding, and pretty prints it.

-- |Own libraries & modules
import DataTypes
import WhileParser        (lineParser)
import ParserM            (runP)
import LiveCoding         (evalAST)
import PrettyPrinter      (prettyPrint)

-- |Haskell libraries
import System.Environment (getArgs)
import System.IO
import Data.Maybe         (fromJust)
import Data.Map           (empty)

-- |Main program
-- |Takes a while program, parses it and livecodes it.
main :: IO ()
main =
    do args <- getArgs
       case args of
            [a] -> do input       <- readFile a
                      let content = concat $ lines input
                      let parsed  = runP lineParser content
                      case parsed of
                          Just ast -> prettyPrint a $ evalAST ast
                          Nothing  -> putStrLn "Error while parsing. Please check your syntax."
            _   -> putStrLn "Error!"
