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
import public Data.AVL.Graph
import public Data.List

import GRL.DSL
import GRL.Model
import GRL.Types.Expr
import GRL.Types.Value

%access public
-- ------------------------------------------------------- [ Element Insertion ]

data ValidGoal : GRLExpr ELEM -> GModel -> Type
  where
    OkayGoal : (n : GRLExpr ELEM)
            -> (m : GModel)
            -> ValidGoal n m


||| Check to see if the element is unique.
|||
isElemUnique : (node : GRLExpr ELEM)
            -> (model : GModel)
            -> Bool
isElemUnique (Element ty t s) m = not $ hasGoal t m
  -- case (hasGoal t m) of
  --   False => Yes (OkayGoal (Element ty t s) m)
  --   True  => No  (believe_me)


-- checkElemDec : (e : GRLExpr ELEM)
--             -> (m : GModel)
--             -> Dec (ValidGoal e m)
-- checkElemDec elem model with (isElemUnique (elem) model)
--   | Yes prf = Yes prf
--   | No  con = No  con

||| Check to see if the element is unique.
|||
%hint
checkElemBool : (node : GRLExpr ELEM)
             -> (model : GModel)
             -> Bool
checkElemBool n m = isElemUnique n m
-- with (checkElemDec n m)
--   | Yes prf = True
--   | No  con = False

-- --------------------------------------------------------------------- [ EOF ]
