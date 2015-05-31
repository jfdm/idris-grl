module GRL.Combinator

import public Data.AVL.Set
import public Data.AVL.Graph
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value
import GRL.Property.Element
import GRL.Property.Intention
import GRL.Property.Structure

%access public

-- ---------------------------------------------------- [ Allowed Constructors ]

||| Create an empty model
emptyModel : GModel
emptyModel = mkEmptyGraph

-- ------------------------------------------------------------- [ Interpreter ]

|||  Interpt the types from the DSL.
interpTy : GRLExprTy -> Type
interpTy ELEM   = GoalNode
interpTy INTENT = GoalEdge
interpTy STRUCT = GoalEdge

||| Convert expressions from the DSL to Nodes or Labels
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

||| Perform the insertion of elements into the model.
private
insertElem : GRLExpr ELEM -> GModel -> GModel
insertElem elem model = addNode (convExpr elem) model

infixl 1 \+\

(\+\) : GModel -> GRLExpr ELEM -> GModel
(\+\) model elem =
  case checkElemBool elem model of
    True  => insertElem elem model
    False => model

-- case (checkElemDec elem model) of
--   Yes prf => insertElem elem model
--   No  con => model

-- --------------------------------------------------------------- [ Intention ]
||| Perform the insertion of label into the model.
private
insertIntention : GRLExpr INTENT -> GModel -> GModel
insertIntention (IntentLink a b x y) model =
    let i = convExpr (IntentLink a b x y) in
    addValueEdge (convExpr y, convExpr x, Just i) model

infixl 1 \->\

(\->\) : GModel -> GRLExpr INTENT -> GModel
(\->\) m i =
  case (checkIntentBool i m) of
    True  => insertIntention i m
    False => m

private
insertStructure : GRLExpr STRUCT -> GModel ->  GModel
insertStructure (StructureLink a x ys) model =
  let i = convExpr (StructureLink a x ys) in
    foldl (\m, y => addValueEdge (convExpr x, convExpr y, Just i) m) model ys

infixl 1 \<-\

(\<-\) : (m : GModel) -> (e : GRLExpr STRUCT) -> GModel
(\<-\) model i =
  case (checkStructBool i model) of
    True  => insertStructure i model
    False => model
-- --------------------------------------------------------------------- [ EOF ]
