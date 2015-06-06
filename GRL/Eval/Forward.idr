 module GRL.Eval.Forward

import Effects
import Effect.State

import Data.AVL.Dependent.Dict
import Data.AVL.Dependent.Graph
import Data.Stack

import GRL.Common
import GRL.Model

import GRL.Eval.Qualitative

%access public

-- ----------------------------------------------------- [ Forward Propagation ]

||| The effects used in a BFS.
MEvalEffs : List EFFECT
MEvalEffs = [ 'next ::: STATE (Stack NodeID)
            , 'seen ::: STATE (List NodeID)]

private
getSat' : NodeID -> GModel -> Satisfaction
getSat' id g =
  case getValueByID id g of
    Nothing => NONE
    Just v  => case sValue v of
      Nothing => NONE
      Just s  => s

calcDecomp : NodeID -> GModel -> Eff (Satisfaction) MEvalEffs
calcDecomp id g = do
    case getValueByID id g of
      Nothing => pure NONE
      Just val =>
        case dTy val of
          NOTTy => pure NONE
          dval  => do
            let cedges   = getEdgesByID id g
            let children = map fst $ filter (\x => isDeCompEdge $ snd x) cedges
            let csat     = map (\x => getSat' x g) children
            let res = case dval of
                      ANDTy => getDecompAnd csat
                      XORTy => getDecompXOR csat
                      IORTy => getDecompIOR csat
            pure res


private
%inline
calcWeightedContrib : DemiEdge GoalEdge -> GModel -> Satisfaction
calcWeightedContrib (id, Nothing)                _ = NONE
calcWeightedContrib (id, Just (Contribution x))  g = weightedContrib (getSat' id g) x
calcWeightedContrib (id, Just (Correlation  x))  g = weightedContrib (getSat' id g) x
calcWeightedContrib _                            _ = NONE

calcContrib : Satisfaction -> NodeID -> GModel -> Eff Satisfaction MEvalEffs
calcContrib dval id g = do
   let cedges = getEdgesByID id g
   let wsat   = map (\e => calcWeightedContrib e g) cedges
   let count' = adjustCounts (dval::wsat)
   if not (noUndec count' > 0)
     then pure UNDECIDED
     else pure $ combineContribs (cmpSatAndDen count') (cmpWSandWD count')

evalElem : NodeID -> GModel -> Eff Satisfaction MEvalEffs
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
          let val = fromMaybe (GNode GOALTy "" Nothing NOTTy) $ getValueByID curr g
          let ns = map fst $ getEdgesByID curr g

          'init :- update (\x => if isCons ns
                    then x
                    else x && isJust (sValue val))

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
              let allSat   = and $ map (\x => isJust (sValue x)) children
              case allSat of
                True => do
                  eval <- evalElem curr g
                  let newG = updateNodeValueByIDUsing curr (\x => record {sValue = Just eval} x) g
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

evalModel : GModel -> List (GoalNode)
evalModel g = with Effects runPureInit
    [ 'next := pushSThings (verticesID g) mkStack
    , 'seen := List.Nil] $ do
        newG <- doEval g
        pure $ (vertices newG)
-- --------------------------------------------------------------------- [ EOF ]
