-- -- -- |Project: Functionele en Logische Programmeertalen
-- -- -- |Deel: Haskell
-- -- -- |Auteur: Tom Naessens
-- -- -- |File: WhileParser
-- -- -- |      Parses an inputfile to an AST

module WhileParser where

import ParserM
import DataTypes

-- |Parses a line: removes the whitespace in front and calls the StatementParser
lineParser :: Parser Stmnt
lineParser = do whiteSpace
                stmntParser

-- |Parses a statement: splits up the 3 possible cases
stmntParser :: Parser Stmnt
stmntParser = assignParser
           \/ whileParser
           \/ seqParser

-- |Parses a sequence of statements
seqParser :: Parser Stmnt
seqParser = do stmnts <- sSeq lineParser
               return $ case stmnts of
                             [x] -> x          {- TN: We don't need a one-sized list! -}
                             _   -> Seq stmnts

-- |Parses an assigment
whileParser :: Parser Stmnt
whileParser = do token "while"
                 whiteSpace
                 cond  <- (parens condParser '(' ')')
                 whiteSpace
                 stmnt <- (parens lineParser '{' '}')
                 return $ While cond stmnt

-- |Parses the conditional while expression
condParser :: Parser CExpr
condParser = do e1 <- exprParser
                wChar '>'
                e2 <- exprParser
                return $ e1 :>: e2

-- |Parses an expression
exprParser :: Parser Expr
exprParser = do x <- term
                expr x
    where
        expr :: Expr -> Parser Expr
        term, factor :: Parser Expr
        expr x = do wChar '+'
                    e <- term
                    expr $ x :+: e
              \/ do wChar '-'
                    e <- term
                    expr $ x :-: e
              \/ return x
        term = do x <- factor
                  char '*'
                  t <- term
                  return $ x :*: t
            \/ factor
        factor = parens exprParser '(' ')'
           \/ do y1 <- number
                 return $ L y1
           \/ do y2 <- sLower
                 return $ Var y2

-- |Parses an assignment
assignParser :: Parser Stmnt
assignParser = do x1 <- sLower
                  wChar '='
                  x2 <- exprParser
                  return $ Assign x1 x2
