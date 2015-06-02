||| This module defines a 'compiler' that transforms the GRL IR into the Goal Graph.
module GRL.Builder

import public Data.AVL.Set
import public Data.AVL.Graph
import public Data.List

import GRL.Model
import GRL.IR
import GRL.Common
import GRL.Property.Element
import GRL.Property.Intention
import GRL.Property.Structure

%access public

-- ---------------------------------------------------- [ Allowed Constructors ]

||| Create an empty model
emptyModel : GModel
emptyModel = mkEmptyGraph

-- ------------------------------------------------------------- [ Interpreter ]

|||  Interpt the IR types to get Goal Graph Types.
interpTy : GrlIRTy -> Type
interpTy ELEM   = GoalNode
interpTy INTENT = GoalEdge
interpTy STRUCT = GoalEdge

||| Convert expressions from the IR to Goal Graph objects.
convExpr : {ty : GrlIRTy} -> GrlIR ty -> interpTy ty
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
insertElem : GrlIR ELEM -> GModel -> GModel
insertElem elem model = addNode (convExpr elem) model

infixl 5 \+\
||| Add elemeents to the model.
(\+\) : GRL expr => GModel -> expr ELEM -> GModel
(\+\) model elem =
    if checkElemBool e' model
      then insertElem e' model
      else model
  where
    e' : GrlIR ELEM
    e' = mkGoal elem

-- --------------------------------------------------------------- [ Intention ]
||| Perform the insertion of label into the model.
private
insertIntention : GrlIR INTENT -> GModel -> GModel
insertIntention (IntentLink a b x y) model =
  addValueEdge (convExpr y, convExpr x, Just i) model
    where
      i : GoalEdge
      i = convExpr (IntentLink a b x y)


infixl 5 \->\

||| Add an intention declaration to the model.
(\->\) : GRL expr => GModel -> expr INTENT -> GModel
(\->\) m i =
    if (checkIntentBool l m)
      then insertIntention l m
      else m
  where
    l : GrlIR INTENT
    l = mkIntent i

-- --------------------------------------------------------------- [ Structure ]
||| Do structure insertion.
private
insertStructure : GrlIR STRUCT -> GModel ->  GModel
insertStructure (StructureLink ty x@(Element _ t _) ys) model =
  let i = convExpr (StructureLink ty x ys) in
    foldl (\m, y => addValueEdge (convExpr x, convExpr y, Just i) m) model ys



infixl 5 \<-\

||| Add a structure declaration to the model
(\<-\) : GRL expr => GModel -> expr STRUCT -> GModel
(\<-\) model i =
    if (checkStructBool s model)
      then insertStructure s model
      else model
  where
    s : GrlIR STRUCT
    s = mkStruct i
-- --------------------------------------------------------------------- [ EOF ]
