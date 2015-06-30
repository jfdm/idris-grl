-- ------------------------------------------------------------- [ Element.idr ]
-- Module    : Element.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

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

import public Data.AVL.Graph
import public Data.List

import GRL.Model
import GRL.IR
import GRL.Common

%access public
-- ------------------------------------------------------- [ Element Insertion ]

||| Check to see if the element is unique.
|||
isElemUnique : (node : GExpr ELEM) -> (model : GModel) -> Bool
isElemUnique (Elem ty t s) m = not $ hasGoal t m

||| Check to see if the element is unique.
|||
%hint
checkElemBool : (node : GExpr ELEM) -> (model : GModel) -> Bool
checkElemBool n m = isElemUnique n m

-- --------------------------------------------------------------------- [ EOF ]
