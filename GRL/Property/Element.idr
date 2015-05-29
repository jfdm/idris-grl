||| This module details correctness properties for element insertion.
|||
||| Correctness/Soundness Properties ::
|||
||| 1. All elements added to the model must be unique.
|||
||| Note ::
|||
||| + This property should probably be replaced within the model using a Set.
|||
module GRL.Property.Element

import public Decidable.Equality

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.List

import GRL.Model
import GRL.Types.Expr
import GRL.Types.Value

-- ------------------------------------------------------- [ Element Insertion ]

data IsUniqueElem : GoalNode -> GModel -> Type
  where
    IsUnique : IsUniqueElem node model


||| Check to see if the element is unique.
|||
isElemUnique : (node : GoalNode)
            -> (model : GModel)
            -> Dec (IsUniqueElem node model)
isElemUnique n m =
  case (hasGoal (getGoalTitle n) m) of
    False => Yes (IsUnique)
    True  => No  (believe_me)


||| Check to see if the element is unique.
|||
isElemUnique' : (node : GoalNode)
             -> (model : GModel)
             -> Bool
isElemUnique' n m with (isElemUnique n m)
  | Yes prf = True
  | No  con = False

-- --------------------------------------------------------------------- [ EOF ]
