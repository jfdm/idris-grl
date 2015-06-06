||| The GRL Model as  Goal Graph
module GRL.Model

import public Data.AVL.Dependent.Graph
import public Data.List

import GRL.Common

import Debug.Trace

%access public

record GoalNode where
  constructor GNode
  nTy : GRLElementTy
  gTitle : String
  sValue : Maybe Satisfaction
  dTy : Decomposition

instance Show GoalNode where
  show (GNode ty n s d) = with List unwords ["[GNode", show ty, n, show s, show d, "]"]

instance Eq GoalNode where
  (==) (GNode xty x xs xd) (GNode yty y ys yd) =
      xty == yty &&
      x   == y   &&
      xs  == ys  &&
      xd  == yd

data GoalEdge  : Type where
  Contribution : ContributionTy -> GoalEdge
  Correlation  : ContributionTy -> GoalEdge
  Decomp       : GoalEdge

instance Show GoalEdge where
  show (Contribution ty) = with List unwords ["[Contrib", show ty, "]"]
  show (Correlation ty)  = with List unwords ["[Correl", show ty, "]"]
  show Decomp            = with List unwords ["[Decomp]"]

instance Eq GoalEdge where
  (==) (Contribution x) (Contribution y) = x == y
  (==) (Correlation x)  (Correlation y)  = x == y
  (==) Decomp           Decomp           = True
  (==) _                _                = False

GModel : Type
GModel = Graph (GoalNode) (GoalEdge)

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
getGoalByTitle t g = getValueUsing (\x => gTitle x == t) g

getGoalByTitle' : GoalNode -> GModel -> Maybe GoalNode
getGoalByTitle' t g = getGoalByTitle (gTitle t) g

hasGoal : String -> GModel -> Bool
hasGoal t m = hasValueUsing (\(x,_) => gTitle x == t) (graph m)


updateGoalNode : (sfunc : GoalNode -> Bool)
              -> (ufunc : GoalNode -> GoalNode)
              -> (model : GModel)
              -> GModel
updateGoalNode f u m =
    case getValueUsing f m of
      Nothing  => m
      Just val => updateNodeValueUsing val u m
