-- -- --| Project: Functionele en Logische Programmeertalen
-- -- --| Deel: Haskell
-- -- --| Auteur: Tom Naessens
-- -- --| File: LiveCoding
-- -- --|       Takes an AST as input and returns stuff

module LiveCoding where
import Prelude hiding (lookup)
import DataTypes
import Data.Map
import Data.Maybe
import Control.Monad.State

-- |Folds an expression
foldExpr :: (Int -> t) ->
           (String -> t) ->
           (t -> t -> t) ->
           (t -> t -> t) ->
           (t -> t -> t) ->
           Expr ->
           t
foldExpr c v a s m =
    go
        where go (L i)       = c i
              go (Var s)     = v s
              go (e1 :+: e2) = a (go e1) (go e2)
              go (e1 :-: e2) = s (go e1) (go e2)
              go (e1 :*: e2) = m (go e1) (go e2)

-- |Evaluates an expression, given a varMap, other modules should call this
-- |instead of foldExpr
eval :: Map String Int -> Expr -> Int
eval varMap = foldExpr id (fromJust . flip lookup varMap) (+) (-) (*)
                          {- TN: We need to flip here, as the variables come in the from position. -}

data StmntState = State (VarMap, StmntList) StmntList

-- |Evaluates an AST, returns a global state
evalAST :: Stmnt -> StmntList
evalAST stmnt = evalState (foldAST assign while stmnt) (empty,  [])

-- |Folds a tree
-- |We use 2 maps here: varMap:   the 'global' state of the variables
-- |                    stmntMap: a map of statements mapped to states
foldAST :: (VarMap -> String -> Expr -> VarMap) ->
           (VarMap -> CExpr -> Stmnt -> Stmnt) ->
           Stmnt ->
           State (VarMap, StmntList) StmntList
foldAST a w = go
    where go (Seq [])             = do
             (varMap, stmntList) <- get
             return stmntList
          go (Seq (stmnt:stmnts)) = do
             (varMap, stmntList) <- get
             case stmnt of
                  Assign var expr ->
                    put (a varMap var expr, stmntList ++ [(stmnt, a varMap var expr)])
                  While cexpr sts -> do
                    let result = w varMap cexpr sts
                    let (insideWhile, s) = runState (go result) (varMap, [])
                    {- I used insideWhile <- go $ w varMap cexpr sts here first, but then I had
                     - scoping. Scoping is nice, but we do not want it here so I ask runState to
                     - give both the resulting varMap and state back, and overwrite the old state. -}
                    let (newMap, _) = s
                    put (newMap, stmntList
                                  ++ [(stmnt, varMap)]
                                  ++ insideWhile
                        )
                  WhileI cexpr sts -> do {- De WhileI en While case lijken hier vrij goed op elkaar,
                                          - voor de deadline kon ik deze echter niet meer samen voegen -}
                    let result = w varMap cexpr sts
                    case result of
                         Seq [WhileE] -> put (varMap, stmntList ++ [(WhileE, varMap)])
                         _            -> do
                                    let (insideWhile, s) = runState (go result) (varMap, [])
                                    let (newMap, _) = s
                                    put (newMap, stmntList
                                                  ++ [(stmnt, varMap)]
                                                  ++ insideWhile
                                        )
                  WhileE -> do
                    put (varMap, stmntList
                                  ++ [(stmnt, varMap)]
                        )

             go $ Seq stmnts
          go expr                 =  {- Bugfix for when we have a program like "x = 2" -}
             go $ Seq [expr]


-- |Assigns an expression: adds/updates the variable to the map
assign :: VarMap -> String -> Expr -> VarMap
assign varMap var expr = insert var (eval varMap expr) varMap

-- |Folds a while open
while :: VarMap -> CExpr -> Stmnt -> Stmnt
while varMap (e1 :>: e2) stmnts =
    if eval varMap e1 > eval varMap e2 then
        case stmnts of                    {- Bugfix to fix infinite recursion -}
            Seq sts -> Seq $ sts ++ [WhileI (e1 :>: e2) stmnts]
            _       -> Seq [stmnts, WhileI (e1 :>: e2) stmnts]
    else
        Seq [WhileE]
