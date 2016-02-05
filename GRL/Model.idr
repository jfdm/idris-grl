-- --------------------------------------------------------------- [ Model.idr ]
-- Module    : Model.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| The GRL Model as  Goal Graph
module GRL.Model

import public Data.AVL.Graph
import public Data.List

import GRL.Common
import Debug.Trace

%access export

-- ------------------------------------------------------------------- [ Nodes ]

||| Nodes in the Goal Graph
public export
record GoalNode where
  constructor GNode
  getNodeTy    : GElemTy
  getNodeTitle : String
  getSValue    : Maybe SValue
  getStructTy  : Maybe GStructTy

Show GoalNode where
  show (GNode ty n s d) = with List unwords ["[GNode", show ty, n, show s, show d, "]"]

Eq GoalNode where
  (==) (GNode xty x xs xd) (GNode yty y ys yd) =
      xty == yty &&
      x   == y   &&
      xs  == ys  &&
      xd  == yd

-- ------------------------------------------------------------------- [ Edges ]

public export
data GoalEdge  : Type where
  Contribution : CValue -> GoalEdge
  Correlation  : CValue -> GoalEdge
  Decomp       : GoalEdge

Show GoalEdge where
  show (Contribution ty) = with List unwords ["[Contrib", show ty, "]"]
  show (Correlation ty)  = with List unwords ["[Correl", show ty, "]"]
  show Decomp            = with List unwords ["[Decomp]"]

Eq GoalEdge where
  (==) (Contribution x) (Contribution y) = x == y
  (==) (Correlation x)  (Correlation y)  = x == y
  (==) Decomp           Decomp           = True
  (==) _                _                = False

-- ---------------------------------------------------------------- [ Synonyms ]

public export
GModel : Type
GModel = Graph (GoalNode) (GoalEdge)

-- ---------------------------------------------------------- [ Util Functions ]

isDeCompEdge : Maybe GoalEdge -> Bool
isDeCompEdge (Just Decomp) = True
isDeCompEdge _             = False

isContribEdge : Maybe GoalEdge -> Bool
isContribEdge (Just (Contribution y)) = True
isContribEdge _                       = False

isCorrelEdge : Maybe GoalEdge -> Bool
isCorrelEdge (Just (Correlation y)) = True
isCorrelEdge _                      = False

getGoalByTitle : String -> GModel -> Maybe GoalNode
getGoalByTitle t g = getValueUsing (\x => getNodeTitle x == t) g

getGoalIDByTitle : String -> GModel -> Maybe NodeID
getGoalIDByTitle t g = getNodeIDUsing (\x => getNodeTitle x == t) g

getGoalByTitle' : GoalNode -> GModel -> Maybe GoalNode
getGoalByTitle' t g = getGoalByTitle (getNodeTitle t) g

hasGoal : String -> GModel -> Bool
hasGoal t m = isJust $ getValueUsing (\x => getNodeTitle x == t) m


updateGoalNode : (sfunc : GoalNode -> Bool)
              -> (ufunc : GoalNode -> GoalNode)
              -> (model : GModel)
              -> GModel
updateGoalNode f u m =
    case getValueUsing f m of
      Nothing  => m
      Just val => updateNodeValueUsing val u m

getDeCompEdges : NodeID -> GModel -> List (DemiEdge GoalEdge)
getDeCompEdges n m = filter (\(y,l) => isDeCompEdge l) cs
  where
    cs : List (DemiEdge GoalEdge)
    cs = getEdgesByID n m

getIntentEdges : NodeID -> GModel -> List (DemiEdge GoalEdge)
getIntentEdges n m = filter (\(y,l) => not (isDeCompEdge l)) cs
  where
    cs : List (DemiEdge GoalEdge)
    cs = getEdgesByID n m
-- --------------------------------------------------------------------- [ EOF ]
