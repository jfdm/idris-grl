||| This section details the combinator for intentional link insertion.
|||
||| Correctness/Soundness Properties of an Intentional Link
|||
||| 1. The link should use elements that are in the model.
||| 2. The destination cannot have type: Resource
||| 3. The src and destination must not be the same.
|||
module GRL.Property.Intention

import public Decidable.Equality

import public Data.AVL.Dependent.Graph
import public Data.List

import GRL.Model
import GRL.IR
import GRL.Common

%access public

-- ---------------------------------------------- [ Intentional Link Insertion ]
examineLink : GExpr INTENT -> Bool
examineLink (ILink cTy c x (Elem RESty n s)) = False
examineLink (ILink cTy c x y)                = not $ eqGExpr x y

inModel : GExpr ELEM -> GModel -> Bool
inModel (Elem ty n s) m = hasGoal n m

validLink : GExpr INTENT -> GModel -> Bool
validLink (ILink cTy ty x y) m = (inModel x m) && (inModel y m)

%hint
checkIntentBool : GExpr INTENT -> GModel -> Bool
checkIntentBool l m = validLink l m && examineLink l

-- --------------------------------------------------------------------- [ EOF ]
