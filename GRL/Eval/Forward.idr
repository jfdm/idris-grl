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
import Data.Queue
import Data.Vect

import GRL.Common
import GRL.Model

import GRL.Eval.Qualitative
import GRL.Eval.Strategy

import Debug.Trace

%access public

-- ----------------------------------------------------- [ Forward Propagation ]

||| The effects used in a BFS.
MEvalEffs : List EFFECT
MEvalEffs = [STATE (Queue NodeID)]

private
getSat' : NodeID -> GModel -> Maybe SValue
getSat' id g =
  case getValueByID id g of
    Nothing => Nothing
    Just v  => getSValue v

calcDecomp : NodeID -> GModel -> Eff (Maybe SValue) MEvalEffs
calcDecomp id g = do
    case getValueByID id g of
      Nothing => pure Nothing
      Just val =>
        case getStructTy val of
          Nothing   => pure Nothing
          Just dval => do
            let cedges   = getEdgesByID id g
            let children = map fst $ filter (\x => isDeCompEdge $ snd x) cedges
            let csat     = catMaybes $ map (\x => getSat' x g) children
            let res = case dval of
                      ANDty => getDecompAnd csat
                      XORty => getDecompXOR csat
                      IORty => getDecompIOR csat
            pure $ Just res



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

calcContrib : Maybe SValue -> NodeID -> GModel -> Eff SValue MEvalEffs
calcContrib dval id g = do
   let cedges   = getEdgesByID id g
   let children = filter (\x => not (isDeCompEdge $ snd x)) cedges
   let wsat     = catMaybes $ map (\e => calcWeightedContrib e g) children
   let vs       = case dval of
       Nothing => wsat
       Just x  => x::wsat
   let count'   = adjustCounts vs
   if (noUndec count' > 0)
     then pure UNDECIDED
     else pure $ combineContribs count'

evalElem : NodeID -> GModel -> Eff SValue MEvalEffs
evalElem e g = do
  decompValue  <- calcDecomp e g
  contribValue <- calcContrib decompValue e g
  pure contribValue

-- -------------------------------------------------------------- [ Init Check ]

validityCheck : GModel -> Bool
validityCheck g = allLeafsValid && not gTy
  where
    allLeafsValid : Bool
    allLeafsValid = and $ map (\x => isJust (getSValue x)) (getValuesByID (leafNodes g) g)

    gTy : Bool
    gTy = isDisconnected g

initGraph : GModel -> GModel
initGraph g = foldl (doUp) g (leaves)
  where
    leaves : List GoalNode
    leaves = map (\x => if isJust (getSValue x) then x else record {getSValue = Just NONE} x) (getValuesByID (leafNodes g) g)

    doUp : GModel -> GoalNode -> GModel
    doUp m n = updateGoalNode (\x => getNodeTitle n == getNodeTitle x)
                              (\x => n)
                              m

partial
doEval : GModel -> Eff GModel MEvalEffs
doEval g = do
  q <- get
  case popQ' q of
    Nothing        => pure g
    Just (c, newQ) => do
      put newQ
      case getValueByID c g of --- if node doesn't exist
        Nothing => pure g
        Just c' => do
          if isJust $ getSValue c' --- if satisfied then move on
            then doEval g
            else do
              let childIDs = getEdgesByID c g
              if isNil childIDs --- if leaf node
                then pure g
                else do
                  let children = getValuesByID (map fst childIDs) g
                  if and $ map (\x => isJust $ getSValue x) children
                    then do
                      eval <- evalElem c g
                      let newG = updateNodeValueByIDUsing c (\x => record {getSValue = Just eval} x) g
                      doEval newG
                    else do
                      update (\xs => pushQ c xs)
                      doEval g

private
partial
runEval : GModel -> List (GoalNode)
runEval g = with Effects
    runPureInit [pushQThings (verticesID g) mkQueue]
                (wrapper g)
  where
    wrapper : GModel -> Eff (List GoalNode) MEvalEffs
    wrapper g =
      case validityCheck g of
        True => do
              newG <- doEval g
              pure (vertices newG)
        False => do
              let g' = initGraph g
              case validityCheck g' of
                True => do
                  newG <- doEval g'
                  pure (vertices newG)
                False => pure Nil

||| Evaluate a model with or without a given strategy.
|||
||| This function will deploy the strategy if it is given. Using this
||| code with a predeployed strategy may give unexpected results.
partial
evalModel : (g : GModel)
         -> Maybe Strategy
         -> List (GoalNode)
evalModel g Nothing  = runEval g
evalModel g (Just s) = runEval $ fst (deployStrategy g s)
-- --------------------------------------------------------------------- [ EOF ]
