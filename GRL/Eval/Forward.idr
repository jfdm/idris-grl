-- ------------------------------------------------------------- [ Forward.idr ]
-- Module    : Forward.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module GRL.Eval.Forward

import Effects
import Effect.State

import Data.AVL.Dict
import Data.AVL.Graph
import Data.Stack

import GRL.Common
import GRL.Model

import GRL.Eval.Qualitative
import GRL.Eval.Strategy

import Debug.Trace

%access public

-- ----------------------------------------------------- [ Forward Propagation ]

||| The effects used in a BFS.
MEvalEffs : List EFFECT
MEvalEffs = [ 'next ::: STATE (Stack NodeID)
            , 'seen ::: STATE (List NodeID)]

private
getSat' : NodeID -> GModel -> Maybe SValue
getSat' id g =
  case getValueByID id g of
    Nothing => Nothing
    Just v  => Just $ getSValue v

calcDecomp : NodeID -> GModel -> Eff (SValue) MEvalEffs
calcDecomp id g = do
    case getValueByID id g of
      Nothing => pure NONE
      Just val =>
        case getStructTy val of
          Nothing   => pure NONE
          Just dval => do
            let cedges   = getEdgesByID id g
            let children = map fst $ filter (\x => isDeCompEdge $ snd x) cedges
            let csat     = catMaybes $ map (\x => getSat' x g) children
            let res = case dval of
                      ANDty => getDecompAnd csat
                      XORty => getDecompXOR csat
                      IORty => getDecompIOR csat
            pure res



getWeightedContrib : NodeID -> CValue -> GModel -> Maybe SValue
getWeightedContrib id y g = case getSat' id g of
  Nothing => Nothing
  Just x  => Just $ weightedContrib x y

private
%inline
calcWeightedContrib : DemiEdge GoalEdge -> GModel -> Maybe SValue
calcWeightedContrib (id, Just (Contribution x))  g = getWeightedContrib id x g
calcWeightedContrib (id, Just (Correlation  x))  g = getWeightedContrib id x g
calcWeightedContrib _                            _ = Nothing

calcContrib : SValue -> NodeID -> GModel -> Eff SValue MEvalEffs
calcContrib dval id g = do
   let cedges   = getEdgesByID id g
   let children = filter (\x => not (isDeCompEdge $ snd x)) cedges
   let wsat     = catMaybes $ map (\e => calcWeightedContrib e g) children
   let count'   = adjustCounts (dval::wsat)
   if (noUndec count' > 0)
     then pure UNKNOWN
     else pure $ combineContribs (cmpWSandWD count') (cmpSatAndDen count')

evalElem : NodeID -> GModel -> Eff SValue MEvalEffs
evalElem e g = do
  decompValue  <- calcDecomp e g
  contribValue <- calcContrib decompValue e g
  pure contribValue

-- --------------------------------------------------- [ Initialisation Checks ]

MInitEffs : List EFFECT
MInitEffs = [ 'next ::: STATE (Stack NodeID)
            , 'seen ::: STATE (List NodeID)
            , 'init ::: STATE Bool]

-- -------------------------------------------------------------- [ Evaluation ]
private
partial
doEval : GModel -> Eff GModel MEvalEffs
doEval g = do
  s <- 'next :- get
  case popS' s of
    Nothing           => pure g
    Just (curr, newS) => do
      'next :- put newS
      vs <- 'seen :- get
      if elem curr vs
        then doEval g
        else do
          let ns = getEdgesByID curr g
          if isNil ns
            then do
              'seen :- update (\xs => [curr] ++ xs)
              doEval g
            else do
              let childIDs = map fst ns
              let children = catMaybes $ map (\x => getValueByID x g) childIDs
              eval <- evalElem curr g
              let newG = updateNodeValueByIDUsing curr (\x => record {getSValue = eval} x) g
              'seen :- update (\xs => [curr] ++ xs)
              doEval newG

private
partial
runEval : GModel -> List (GoalNode)
runEval g = with Effects runPureInit [ 'next := pushSThings (verticesID g) mkStack
                                     , 'seen := List.Nil] $ do
    newG <- doEval g
    pure (vertices newG)

||| Evaluate a model with or without a given strategy.
|||
||| This function will deploy the strategy if it is given. Using this
||| code with a predeployed strategy may give unexpected results.
partial
evalModel : GModel -> Maybe Strategy -> List (GoalNode)
evalModel g Nothing  = runEval g
evalModel g (Just s) = runEval $ fst (deployStrategy g s)
-- --------------------------------------------------------------------- [ EOF ]
