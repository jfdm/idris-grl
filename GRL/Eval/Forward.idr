 module GRL.Eval.Forward

import Effects
import Effect.State

import Data.AVL.Dependent.Dict
import Data.AVL.Dependent.Graph
import Data.Stack

import GRL.Common
import GRL.Model

import GRL.Eval.Qualitative
import GRL.Eval.Strategy

%access public

-- ----------------------------------------------------- [ Forward Propagation ]

||| The effects used in a BFS.
MEvalEffs : List EFFECT
MEvalEffs = [ 'next ::: STATE (Stack NodeID)
            , 'seen ::: STATE (List NodeID)]

private
getSat' : NodeID -> GModel -> SValue
getSat' id g =
  case getValueByID id g of
    Nothing => NONE
    Just v  => case getSValue v of
      Nothing => NONE
      Just s  => s

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
            let csat     = map (\x => getSat' x g) children
            let res = case dval of
                      ANDty => getDecompAnd csat
                      XORty => getDecompXOR csat
                      IORty => getDecompIOR csat
            pure res


private
%inline
calcWeightedContrib : DemiEdge GoalEdge -> GModel -> SValue
calcWeightedContrib (id, Nothing)                _ = NONE
calcWeightedContrib (id, Just (Contribution x))  g = weightedContrib (getSat' id g) x
calcWeightedContrib (id, Just (Correlation  x))  g = weightedContrib (getSat' id g) x
calcWeightedContrib _                            _ = NONE

calcContrib : SValue -> NodeID -> GModel -> Eff SValue MEvalEffs
calcContrib dval id g = do
   let cedges = getEdgesByID id g
   let wsat   = map (\e => calcWeightedContrib e g) cedges
   let count' = adjustCounts (dval::wsat)
   if not (noUndec count' > 0)
     then pure UNDECIDED
     else pure $ combineContribs (cmpSatAndDen count') (cmpWSandWD count')

evalElem : NodeID -> GModel -> Eff SValue MEvalEffs
evalElem e g = do
  decompValue  <- calcDecomp e g
  contribValue <- calcContrib decompValue e g
  pure contribValue


MInitEffs : List EFFECT
MInitEffs = [ 'next ::: STATE (Stack NodeID)
            , 'seen ::: STATE (List NodeID)
            , 'init ::: STATE Bool]
private
doinitValid : GModel -> Eff () MInitEffs
doinitValid g = do
  s <- 'next :- get
  case popS' s of
    Nothing           => pure ()
    Just (curr, newS) => do
      'next :- put newS
      vs <- 'seen :- get
      if elem curr vs
        then doinitValid g
        else do
          let val = fromMaybe (GNode GOALty "" Nothing Nothing) $ getValueByID curr g
          let ns = map fst $ getEdgesByID curr g

          'init :- update (\x => if isCons ns
                    then x
                    else x && isJust (getSValue val))

          'seen :- update (\xs => [curr] ++ xs)
          'next :- update (\xs => pushSThings ns s)
          doinitValid g

private
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
          case getEdgesByID curr g of
            Nil => do
              'seen :- update (\xs => [curr] ++ xs)
              doEval g
            ns  => do
              let childIDs = map fst ns
              let children = catMaybes $ map (\x => getValueByID x g) childIDs
              let allSat   = and $ map (\x => isJust (getSValue x)) children
              case allSat of
                True => do
                  eval <- evalElem curr g
                  let newG = updateNodeValueByIDUsing curr (\x => record {getSValue = Just eval} x) g
                  'seen :- update (\xs => [curr] ++ xs)
                  doEval newG
                False => do
                  'next :- update (\xs => pushSThings childIDs s)
                  doEval g

validInit : GModel -> Bool
validInit g = with Effects runPureInit
    [ 'next := pushSThings (verticesID g) mkStack
    , 'seen := List.Nil
    , 'init := True] $ (do
        doinitValid g
        res <- ('init :- get)
        pure res)

private
runEval : GModel -> List (GoalNode)
runEval g = with Effects runPureInit [ 'next := pushSThings (verticesID g) mkStack
                                     , 'seen := List.Nil] $ do
        newG <- doEval g
        pure $ (vertices newG)

||| Evaluate a model with or without a given strategy.
|||
||| This function will deploy the strategy if it is given. Using this
||| code with a predeployed strategy may give unexpected results.
evalModel : GModel -> Maybe Strategy -> List (GoalNode)
evalModel g Nothing  = runEval g
evalModel g (Just s) = runEval $ fst (deployStrategy g s)
-- --------------------------------------------------------------------- [ EOF ]
