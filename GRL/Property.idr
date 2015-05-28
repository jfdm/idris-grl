module GRL.Property

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

import public GRL.Property.Common
import public GRL.Property.Element
--import public GRL.Property.Structure
--import public GRL.Property.Intention


checkInsert : (i : GRLExpr ty)
           -> (m : GModel)
           -> Maybe (ValidInsert ty i m)
checkInsert {ty=ELEM}   e m = (checkElem e m)
checkInsert {ty=INTENT} e m = Nothing -- es (IntentInsert)
checkInsert {ty=STRUCT} e m = Nothing -- es (StructInsert)

-- --------------------------------------------------------------------- [ EOF ]
