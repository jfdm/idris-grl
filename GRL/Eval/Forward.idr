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

-- ------------------------------------------------------------- [ Eval Result ]

data EvalResult : Type where
  Result   : List GoalNode  -> EvalResult
  BadModel : EvalResult

-- ----------------------------------------------------- [ Forward Propagation ]

private
getSat' : NodeID -> GModel -> Maybe SValue
getSat' id g =
  case getValueByID id g of
    Nothing => Nothing
    Just v  => getSValue v

calcDecomp : NodeID -> GModel -> Maybe SValue
calcDecomp id g =
    case getValueByID id g of
      Nothing  => Nothing
      Just val =>
        case getStructTy val of
          Nothing   => Nothing
          Just dval =>
            case dval of
              ANDty => Just $ getDecompAnd csat
              XORty => Just $ getDecompXOR csat
              IORty => Just $ getDecompIOR csat
  where
    children : List NodeID
    children = map fst $ filter (\x => isDeCompEdge $ snd x) (getEdgesByID id g)

    csat : List SValue
    csat = catMaybes $ map (\x => getSat' x g) children


getWeightedContrib : NodeID -> CValue -> GModel -> Maybe SValue
getWeightedContrib id y g = case getSat' id g of
  Nothing => Nothing
  Just x  => Just $ weightedContrib x y


calcWeightedContrib : DemiEdge GoalEdge -> GModel -> Maybe SValue
calcWeightedContrib (id, Just (Contribution x))  g = getWeightedContrib id x g
calcWeightedContrib (id, Just (Correlation  x))  g = getWeightedContrib id x g
calcWeightedContrib _                            _ = Nothing

calcContrib : Maybe SValue -> NodeID -> GModel -> SValue
calcContrib dval id g =
    if (noUndec count > 0)
      then UNDECIDED
      else combineContribs count
  where
    children : List (DemiEdge GoalEdge)
    children = filter (\x => not (isDeCompEdge $ snd x)) (getEdgesByID id g)

    wsat : List SValue
    wsat = catMaybes $ map (\e => calcWeightedContrib e g) children

    vals : List SValue
    vals = case dval of
      Nothing => wsat
      Just x  => x :: wsat

    count : ContribCount
    count = adjustCounts vals

evalElem : NodeID -> GModel -> SValue
evalElem e g = calcContrib dVal e g
  where
    dVal : Maybe SValue
    dVal = (calcDecomp e g)

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

-- ------------------------------------------------------- [ Forward Algorithm ]
||| The effects used in a BFS.
MEvalEffs : List EFFECT
MEvalEffs = [STATE (Queue NodeID)]

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
                      let eval = evalElem c g
                      let newG = updateNodeValueByIDUsing c (\x => record {getSValue = Just eval} x) g
                      doEval newG
                    else do
                      update (\xs => pushQ c xs)
                      doEval g

private
partial
runEval : GModel -> EvalResult
runEval g = with Effects
    runPureInit [pushQThings (verticesID g) mkQueue]
                (wrapper g)
  where
    wrapper : GModel -> Eff EvalResult MEvalEffs
    wrapper g =
      case validityCheck g of
        True => do
              newG <- doEval g
              pure $ Result (vertices newG)
        False => do
              let g' = initGraph g
              case validityCheck g' of
                True => do
                  newG <- doEval g'
                  pure $ Result (vertices newG)
                False => pure BadModel

||| Evaluate a model with or without a given strategy.
|||
||| This function will deploy the strategy if it is given. Using this
||| code with a predeployed strategy may give unexpected results.
partial
evalModel : (g : GModel)
         -> Maybe Strategy
         -> EvalResult -- List (GoalNode)
evalModel g Nothing  = runEval g
evalModel g (Just s) = runEval $ fst (deployStrategy g s)
-- --------------------------------------------------------------------- [ EOF ]
