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

import GRL.Model
import GRL.IR
import GRL.Common

%access public
-- ------------------------------------------------------- [ Element Insertion ]

||| Check to see if the element is unique.
|||
isElemUnique : (node : GrlIR ELEM)
            -> (model : GModel)
            -> Bool
isElemUnique (Element ty t s) m = not $ hasGoal t m

||| Check to see if the element is unique.
|||
%hint
checkElemBool : (node : GrlIR ELEM)
             -> (model : GModel)
             -> Bool
checkElemBool n m = isElemUnique n m

-- --------------------------------------------------------------------- [ EOF ]
