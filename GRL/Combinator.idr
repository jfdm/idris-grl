module GRL.Combinator

import public Decidable.Equality

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value
import GRL.Property.Element

%access public

-- ---------------------------------------------------- [ Allowed Constructors ]
emptyModel : GModel
emptyModel = mkEmptyGraph

-- --------------------------------------------------------------- [ Insertion ]
%inline
mkGoalNode : GRLExpr ELEM -> Node -> GoalNode
mkGoalNode (Element ety t s) l =
  case ety of
    GOALTy => Goal l t s Nothing
    SOFTTy => Soft l t s Nothing
    TASKTy => Task l t s Nothing
    RESOURCETy  => Res  l t s Nothing

-- addElem :  (i : GRLExpr ELEM)
--         -> (m : GModel)
--         -> GModel
-- addElem i g = if (checkElem i g )
--   then addNode (mkGoalNode i (counter g)) g
--   else g

addElem' : (i : GRLExpr ELEM)
        -> (m : GModel)
        -> {auto prf : ValidElem i m }
        -> GModel
addElem' i g = addNode (mkGoalNode i (counter g)) g

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
