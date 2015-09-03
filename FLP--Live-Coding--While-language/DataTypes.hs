-- -- -- |Project: Functionele en Logische Programmeertalen
-- -- -- |Deel: Haskell
-- -- -- |Auteur: Tom Naessens
-- -- -- |File: Data
-- -- -- |      Gathers all the data types in one handy file!

module DataTypes where

import Data.Map

-- -- |Statements:
data Stmnt = Seq [Stmnt]
           | Assign String Expr
           | While CExpr Stmnt
           | WhileE                -- The end of a while loop
           | WhileI CExpr Stmnt    -- An iteration of a while loop
             deriving (Show)

 -- -- |Expressions

 -- |Binary operations
data Expr = L Int            -- literals
          | Var String       -- variables
          | Expr :+: Expr    -- additions
          | Expr :-: Expr    -- substractions
          | Expr :*: Expr    -- multiplications
            deriving (Show)

-- |Conditional operations
data CExpr = Expr :>: Expr
             deriving (Show)

type VarMap = Map String Int
type StmntList = [(Stmnt, VarMap)]
