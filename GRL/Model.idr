module GRL.Model

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.SigmaList
import public Data.List

import GRL.Types.Expr
import GRL.Types.Value

%access public

data GoalNode : Type where
  Goal : Node -> String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Soft : Node -> String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Task : Node -> String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Res  : Node -> String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode

private
showNode : GRLElementTy -> Node -> String -> Maybe Satisfaction -> Maybe GRLStructTy -> String
showNode ty l t s d = unwords ["[", show ty, show l, t, show s, show d, "]"]

instance Show GoalNode where
  show (Goal l t s d) = showNode GOAL     l t s d
  show (Soft l t s d) = showNode SOFT     l t s d
  show (Task l t s d) = showNode TASK     l t s d
  show (Res  l t s d) = showNode RESOURCE l t s d

instance Eq GoalNode where
  (==) (Goal i x xs xd) (Goal j y ys yd) = x == y && xs == ys && xd == yd && i == j
  (==) (Soft i x xs xd) (Soft j y ys yd) = x == y && xs == ys && xd == yd && i == j
  (==) (Task i x xs xd) (Task j y ys yd) = x == y && xs == ys && xd == yd && i == j
  (==) (Res  i x xs xd) (Res  j y ys yd) = x == y && xs == ys && xd == yd && i == j
  (==) _              _              = False

getGoalTitle : GoalNode -> String
getGoalTitle (Goal _ t _ _) = t
getGoalTitle (Soft _ t _ _) = t
getGoalTitle (Task _ t _ _) = t
getGoalTitle (Res  _ t _ _) = t

data GoalEdge  : Type where
  Contribution : ContributionTy -> GoalEdge
  Correlation  : ContributionTy -> GoalEdge
  And          : GoalEdge
  Xor          : GoalEdge
  Ior          : GoalEdge

instance Show GoalEdge where
  show (Contribution ty) = unwords ["[Contrib", show ty, "]"]
  show (Correlation ty)  = unwords ["[Correl", show ty, "]"]
  show And       = unwords ["[Edge IOR]"]
  show Xor       = unwords ["[Edge XOR]"]
  show Ior       = unwords ["[Edge AND]"]

GModel : Type
GModel = Graph (GoalNode) (GoalEdge)

hasGoal : String -> GModel -> Bool
hasGoal t m = hasValueUsing (\(x,_) => getGoalTitle x == t) (graph m)
