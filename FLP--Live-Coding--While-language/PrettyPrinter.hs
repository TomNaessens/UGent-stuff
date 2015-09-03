-- -- --| Project: Functionele en Logische Programmeertalen
-- -- --| Deel: Haskell
-- -- --| Auteur: Tom Naessens
-- -- --| File: PrettyPrinter
-- -- --|       Takes a list of tuples and pretty prints it.

module PrettyPrinter where

import DataTypes
import LiveCoding (eval)

import Prelude    hiding (lookup)
import Data.Maybe (fromJust)
import Data.Map   (lookup, toList)
import Data.Char  (isLetter)

-- |Takes a title and a list of statements, makes up the basic output and
-- |delegates the rest of the output
prettyPrint :: String -> StmntList -> IO ()
prettyPrint title l = do
    putStrLn "<html>"
    putStrLn "<head>"
    putStrLn $ "<title>" ++ title ++ "</title>"
    putStrLn "<link rel=\"stylesheet\" type=\"text/css\" href=\"libs/styles.css\" />"
    putStrLn "<script type=\"text/javascript\" src=\"libs/jquery.min.js\"></script>"
    putStrLn "<script type=\"text/javascript\">"
    putStrLn "\tjQuery(\".while\").live('click', function(){"
    putStrLn "\t\tjQuery(this).next(\"span\").slideToggle(\"fast\");"
    putStrLn "\t});"
    putStrLn "</script>"
    putStrLn "</head>"
    putStrLn "<body>"
    putStrLn $ "<h1>" ++ title  ++ "</h1>"
    putStrLn "<pre>"
    prettyPrint' 0 l
    putStrLn "</pre>"
    putStrLn "</body>"
    putStrLn "</html>"

-- |Indentation added to the output, splits up the output in 2 cases
prettyPrint' :: Int -> StmntList -> IO ()
prettyPrint' _ []     = return ()
prettyPrint' i (l:ls) = do
    putStr $ replicate i '\t'
    case l of
        (Assign var expr,    varMap) -> do prettyAssign l
                                           prettyPrint' i ls
        (While cexpr stmnt,  varMap) -> prettyWhile i l ls
        (WhileE,             varMap) -> do putStrLn "</span>"
                                           putStrLn $ replicate (i-1) '\t' ++ "<b>}</b>"
                                           prettyPrint' (i-1) ls
        (WhileI cexpr stmnt, varMap) -> prettyWhileI i l ls

-- |A pretty assignment printer!
prettyAssign :: (Stmnt, VarMap) -> IO ()
prettyAssign (Assign var expr, varMap) = putStrLn $
       "<b>"
    ++ var
    ++ " = "
    ++ prettyExpr expr
    ++ "</b><span class=\"vars\"> | "
    ++ getVar var varMap
    ++ "</span>"

-- |We need a pretty while printer too :3
prettyWhile :: Int -> (Stmnt, VarMap) -> StmntList -> IO ()
prettyWhile i (While (e1 :>: e2) stmnts, varMap) l = do
        putStrLn "<br />"
        putStrLn $ replicate i '\t' ++ "<span class=\"while\">"
             ++ "&#9660; <b>while"
             ++ " ("
             ++ prettyCondExpr e1 e2
             ++ ") "
             ++ "{</b>"
             ++ "<span class=\"vars\">"
             ++ prettyVarMap (toList varMap)
             ++ "</span>"
             ++ "</span>"
        putStrLn $ replicate i '\t' ++ "<span>"

        prettyPrint' (i+1) l

-- |We need a pretty while printer too :3
prettyWhileI :: Int -> (Stmnt, VarMap) -> StmntList -> IO ()
prettyWhileI i (WhileI (e1 :>: e2) stmnts, varMap) l = do
        putStrLn $
            "<br />" ++ replicate i '\t' ++ "While iteration:"
         ++ "<span class=\"vars\">" ++ prettyVarMap (toList varMap) ++ "</span>"
        prettyPrint' (i) l

-- |Prints the variable maps next to a while statement
prettyVarMap :: [(String, Int)] -> String
prettyVarMap []                 = []
prettyVarMap ((var, number):ls) = " | " ++ var ++ " = " ++ show number ++ prettyVarMap ls

-- |Prints a prettay prettay expression
prettyExpr :: Expr -> String
prettyExpr = prettyFoldExpr show id " + " " - " " * "

-- |With a fold of course!
prettyFoldExpr :: (Int -> [a]) ->
                  (String -> [a]) ->
                  [a] ->
                  [a] ->
                  [a] ->
                  Expr ->
                  [a]
prettyFoldExpr l v a s m =
    go
       where go (L int)     = l int
             go (Var str)   = v str
             go (e1 :+: e2) = go e1 ++ a ++ go e2
             go (e1 :-: e2) = go e1 ++ s ++ go e2
             go (e1 :*: e2) = go e1 ++ m ++ go e2

-- |Prints a conditional expression, uses the pretty expression printer
prettyCondExpr :: Expr -> Expr -> String
prettyCondExpr e1 e2 = prettyExpr e1 ++ " > " ++ prettyExpr e2

-- | Takes a variable out of a map and prints it nicely.
getVar :: String -> VarMap -> String
getVar var varMap = var ++ " = " ++ show (fromJust $ lookup var varMap)
