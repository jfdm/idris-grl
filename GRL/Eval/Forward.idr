-- ------------------------------------------------------------- [ Forward.idr ]
-- Module    : Forward.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module GRL.Eval.Forward

import Data.AVL.Dict
import Data.AVL.Graph
import Data.Stack
import Data.Queue
import Data.Vect

import GRL.Common
import GRL.Model

import GRL.Eval.Qualitative
import GRL.Eval.Strategy
import GRL.Eval.Common

%default partial
%access public

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
    children = map fst $ getDeCompEdges id g

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
    children = getIntentEdges id g

    wsat : List SValue
    wsat = catMaybes $ map (\e => calcWeightedContrib e g) children

    vals : List SValue
    vals = case dval of {Nothing => wsat; Just x  => x :: wsat}

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

partial
doEval : GModel -> (Queue NodeID) -> GModel
doEval g q =
    case popQ' q of
      Nothing        => g
      Just (c, newQ) => --  TODO
        case getValueByID c g of --- if node doesn't exist
          Nothing => g
          Just c' =>
            if isJust $ getSValue c' --- if satisfied then move on
              then doEval g newQ
              else let cs = children c in
                if isNil cs --- if leaf node
                  then g
                  else do
                    if and $ map (\x => isJust $ getSValue x) cs
                      then doEval (newG c) newQ
                      else doEval g        (pushQ c newQ)
  where
    childrenIDs : NodeID -> List (DemiEdge GoalEdge)
    childrenIDs n = (getEdgesByID n g)

    children : NodeID -> List GoalNode
    children n = getValuesByID (map fst $ childrenIDs n) g

    newG : NodeID -> GModel
    newG n = updateNodeValueByIDUsing
                   n
                   (\x => record {getSValue = Just (evalElem n g)} x)
                   g

private
partial
runEval : GModel -> EvalResult
runEval g =
    if validityCheck g
        then Result (vertices (doEval g (defQueue g)))
        else let newG = getNewG g in
             let theQ = defQueue newG in
          if validityCheck newG
            then Result (vertices (doEval newG theQ))
            else BadModel
  where
    getNewG : GModel -> GModel
    getNewG m = initGraph m

    defQueue : GModel -> Queue NodeID
    defQueue m = (pushQThings (verticesID m) mkQueue)

||| Evaluate a model with or without a given strategy.
|||
||| This function will deploy the strategy if it is given. Using this
||| code with a predeployed strategy may give unexpected results.
partial
forwardEval : Maybe Strategy -> GModel -> EvalResult
forwardEval Nothing  g = runEval g
forwardEval (Just s) g = runEval $ fst (deployStrategy g s)
-- --------------------------------------------------------------------- [ EOF ]
