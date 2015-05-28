module GRL.Model

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.SigmaList
import public Data.List

import GRL.Types.Expr
import GRL.Types.Value

%access public

data GoalNode : Type where
  Goal : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Soft : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Task : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode
  Res  : String -> Maybe Satisfaction -> Maybe GRLStructTy -> GoalNode

private
showNode : GRLElementTy -> String -> Maybe Satisfaction -> Maybe GRLStructTy -> String
showNode ty t s d = unwords ["[", show ty, t, show s, show d, "]"]

instance Show GoalNode where
  show (Goal t s d) = showNode GOALTy     t s d
  show (Soft t s d) = showNode SOFTTy     t s d
  show (Task t s d) = showNode TASKTy     t s d
  show (Res  t s d) = showNode RESOURCETy t s d

instance Eq GoalNode where
  (==) (Goal x xs xd) (Goal y ys yd) = x == y && xs == ys && xd == yd
  (==) (Soft x xs xd) (Soft y ys yd) = x == y && xs == ys && xd == yd
  (==) (Task x xs xd) (Task y ys yd) = x == y && xs == ys && xd == yd
  (==) (Res  x xs xd) (Res  y ys yd) = x == y && xs == ys && xd == yd
  (==) _              _              = False

getGoalTitle : GoalNode -> String
getGoalTitle (Goal t s d) = t
getGoalTitle (Soft t s d) = t
getGoalTitle (Task t s d) = t
getGoalTitle (Res  t s d) = t

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
