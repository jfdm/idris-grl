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

import Debug.Trace

%access public

-- ---------------------------------------------- [ Intentional Link Insertion ]
data ValidIntent : GrlIR INTENT -> GModel -> Type
  where
    OkayIntent : (i : GrlIR INTENT)
              -> (m : GModel)
              -> ValidIntent i m

examineLink : GrlIR INTENT -> Bool
examineLink (IntentLink cTy c x y) = case (y) of
   (Element ty n s) => case ty of
        RESOURCETy => False
        otherwise  => not $ eqGrlIR x y

inModel : GrlIR ELEM -> GModel -> Bool
inModel (Element ty n s) m = hasGoal n m

validLink : (i : GrlIR INTENT) -> (m : GModel) -> Bool
validLink (IntentLink cTy ty x y) m = (inModel x m) && (inModel y m)

%hint
checkIntentBool : (link : GrlIR INTENT)
              -> (model : GModel)
              -> Bool
checkIntentBool l m = validLink l m && examineLink l

-- --------------------------------------------------------------------- [ EOF ]
