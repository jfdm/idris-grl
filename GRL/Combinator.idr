module GRL.Combinator

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

||| Create an empty model
emptyModel : GModel
emptyModel = mkEmptyGraph

-- ------------------------------------------------------------- [ Interpreter ]

interpTy : GRLExprTy -> Type
interpTy ELEM   = GoalNode
interpTy INTENT = GoalEdge
interpTy STRUCT = GoalEdge


convExpr : {ty : GRLExprTy} -> GRLExpr ty -> interpTy ty
convExpr (Element eTy t s) =
  case eTy of
    GOALTy      => Goal t s Nothing
    SOFTTy      => Soft t s Nothing
    TASKTy      => Task t s Nothing
    RESOURCETy  => Res  t s Nothing
convExpr (IntentLink ty cTy _ _) =
  case ty of
    CONTRIBUTION => Contribution cTy
    CORRELATION  => Correlation  cTy
convExpr (StructureLink ty _ _) =
  case ty of
    ANDTy => And
    XORTy => Xor
    IORTy => Ior

-- --------------------------------------------------------------- [ Insertion ]

insertElem : (expr : GRLExpr ELEM)
          -> (model : GModel)
          -> GModel
insertElem elem model =
  let e = convExpr elem in
    if isElemUnique' e model
      then addNode e model
      else model

-- insertIntention : (expr : GRLExpr INTENT)
--                -> (model : GModel)
--                -> GModel
-- insertIntention link model =
--   let i = convExpr link in
--     if validIntent i model
--       then

-- --------------------------------------------------------------------- [ EOF ]
