module GRL.Property.Common

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

-- --------------------------------------------------- [ Valid Insertion Proof ]
||| Predicate to denote valid insertion of an item into the model.
data ValidInsert : (ty : GRLExprTy)
                -> GRLExpr ty
                -> GModel
                -> Type
  where
    ElemInsert   : ValidInsert ELEM i m
    IntentInsert : ValidInsert INTENT i m
    StructInsert : ValidInsert STRUCT i m

-- --------------------------------------------------------------------- [ EOF ]
