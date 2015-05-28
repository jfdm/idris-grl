module GRL.Property.Element

import public Decidable.Equality

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

import public GRL.Property.Common

-- ------------------------------------------------------- [ Element Insertion ]
-- This section details the property checks for element insertion.

||| Correctness/Soundness Properties ::
|||
||| 1. All elements added to the model must be unique.
|||
||| Note ::
|||
||| + This property should probably be replaced within the model using a Set.
|||
checkElem : (i : GRLExpr ELEM)
         -> (m : GModel)
         -> Maybe (ValidInsert ELEM i m)
checkElem (Element ty t s) m =
  case (hasGoal t m) of
     Nothing => Just (ElemInsert)
     Just n  => Nothing -- No  (believe_me)

-- --------------------------------------------------------------------- [ EOF ]
