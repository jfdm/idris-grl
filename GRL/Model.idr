module GRL.Model

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.SigmaList
import public Data.List

import GRL.Types.Expr
import GRL.Types.Value

data GoalNode : Type where
  Goal : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Soft : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Task : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Res  : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode

instance Eq GoalNode where
  (==) (Goal x xs xd) (Goal y ys yd) = x == y && xs == ys && xd == yd
  (==) (Soft x xs xd) (Soft y ys yd) = x == y && xs == ys && xd == yd
  (==) (Task x xs xd) (Task y ys yd) = x == y && xs == ys && xd == yd
  (==) (Res  x xs xd) (Res  y ys yd) = x == y && xs == ys && xd == yd
  (==) _              _              = False

getGoalTitle : GoalNode -> String
getGoalTitle (Goal t _ _) = t
getGoalTitle (Soft t _ _) = t
getGoalTitle (Task t _ _) = t
getGoalTitle (Res  t _ _) = t

data GoalEdge  : Type where
  Contribution : ContributionTy -> GoalEdge
  Correlation  : ContributionTy -> GoalEdge
  And          : GoalEdge
  Xor          : GoalEdge
  Ior          : GoalEdge

record GModel where
  constructor MkModel
  counter : Nat
  model : Graph (GoalNode) (GoalEdge)

hasGoal : String -> GModel -> Maybe GoalNode
hasGoal t m = hasValueBy (\(x,_) => getGoalTitle x == t) (model m)
