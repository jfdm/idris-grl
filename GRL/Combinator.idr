module GRL.Combinator

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value
import public GRL.Property.Element

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

public
insertElem : (e : GRLExpr ELEM)
          -> (m : GModel)
          -> (prf : IsUniqueElem (convExpr e) m)
          -> GModel
insertElem elem model prf = addNode (convExpr elem) model

infixl 5 \+\

(\+\) : (m : GModel)
     -> (e : GRLExpr ELEM)
     -> {ok : IsUniqueElem (convExpr e) m}
     -> {auto prf : isElemUnique (convExpr e) m = Yes ok}
     -> GModel
(\+\) model elem {ok} = insertElem elem model ok

-- --------------------------------------------------------------- [ Intention ]

insertIntention : GRLExpr INTENT -> GModel -> GModel
insertIntention link@(IntentLink _ _ x y) model =
  let i = convExpr link in
    addValueEdge (convExpr y, convExpr x, Just i) model

infixl 4 \->\

(\->\) : GModel -> GRLExpr INTENT -> GModel
(\->\) m i = insertIntention i m


insertStructure : GRLExpr STRUCT -> GModel ->  GModel
insertStructure link@(StructureLink _ x ys) model =
  let i = convExpr link in
    foldl (\m, y => addValueEdge (convExpr x, convExpr y, Just i) m) model ys

infixl 4 \<-\

(\<-\) : GModel -> GRLExpr STRUCT -> GModel
(\<-\) m i = insertStructure i m
-- --------------------------------------------------------------------- [ EOF ]
