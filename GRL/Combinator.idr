module GRL.Combinator

import public Decidable.Equality

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value
import GRL.Property

%access public

-- ---------------------------------------------------- [ Allowed Constructors ]
emptyModel : GModel
emptyModel = mkEmptyGraph

-- --------------------------------------------------------------- [ Insertion ]
mkGoalNode : GRLExpr ELEM -> Node -> GoalNode
mkGoalNode (Element ety t s) l =
  case ety of
    GOAL => Goal l t s Nothing
    SOFT => Soft l t s Nothing
    TASK => Task l t s Nothing
    RES  => Res  l t s Nothing

-- -------------------------------------------------------- [ Group the Checks ]
private
insert : (item : GRLExpr ty)
      -> (model : GModel)
--      -> (prf : ValidInsert ty item model)
      -> GModel
insert {ty=ELEM}  e g@(MkGraph i d) = addNode (mkGoalNode e i) g
insert {ty=INTENT} i m  = m
insert {ty=STRUCT} s m  = m

infixl 4 /+/

(/+/) : (model : GModel)
     -> (item : GRLExpr ty)
--     -> {auto prf : ValidInsert ty item model}
     -> GModel
(/+/) m i with (checkInsert i m)
  | Yes prf = insert i m
  | No  con = m

-- ---------------------------------------------------------- [ Combine Models ]
-- private
-- insertModel : GModel MODEL
--            -> GModel MODEL
--            -> GModel MODEL
-- insertModel (GRLSpec xs ys zs) g =
--   let g'  = foldr (\e, m => insertElem e m) g xs   in
 --   let g'' = foldr (insertILink) g' ys in
--       foldr insertSLink g'' zs


-- --------------------------------------------------------------------- [ EOF ]
