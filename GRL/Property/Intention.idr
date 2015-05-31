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

import public Data.AVL.Graph
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

%access public

-- ---------------------------------------------- [ Intentional Link Insertion ]
data ValidIntent : GRLExpr INTENT -> GModel -> Type
  where
    OkayIntent : (i : GRLExpr INTENT)
              -> (m : GModel)
              -> ValidIntent i m

examineLink : GRLExpr INTENT -> Bool
examineLink (IntentLink cTy c x y) = case (y) of
   (Element ty n s) => case ty of
        RESOURCETy => False
        otherwise  => not $ eqGRLExpr x y

inModel : GRLExpr ELEM -> GModel -> Bool
inModel (Element ty n s) m = hasGoal n m

validLink : (i : GRLExpr INTENT) -> (m : GModel) -> Bool
validLink (IntentLink cTy ty x y) m = (inModel x m) && (inModel y m)

-- checkIntentDec : (link : GRLExpr INTENT)
--               -> (model : GModel)
--               -> Dec (ValidIntent link model)
-- checkIntentDec l m = validLink l m

%hint
checkIntentBool : (link : GRLExpr INTENT)
              -> (model : GModel)
              -> Bool
checkIntentBool l m = validLink l m && examineLink l

-- --------------------------------------------------------------------- [ EOF ]
