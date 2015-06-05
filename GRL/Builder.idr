||| This module defines a 'compiler' that transforms the GRL IR into the Goal Graph.
module GRL.Builder

import public Data.AVL.Dependent.Graph
import public Data.List

import GRL.Model
import GRL.IR
import GRL.Common
import GRL.Property.Element
import GRL.Property.Intention
import GRL.Property.Structure

import Debug.Trace

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
convExpr (Element eTy t s)       = GNode eTy t s NOTTy
convExpr (IntentLink ty cTy _ _) =
  case ty of
    CONTRIBUTION => Contribution cTy
    CORRELATION  => Correlation  cTy
convExpr (StructureLink _ _ _) = Decomp

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

-- ------------------------------------------------------------------- [ Links ]
private
insertLink : GrlIR ELEM -> GrlIR ELEM -> Maybe GoalEdge -> GModel -> GModel
insertLink (Element _ x _) (Element _ y _) i m =
  case getGoalByTitle x m of
    Nothing  => m
    Just xID =>
      case getGoalByTitle y m of
        Nothing  => m
        Just yID => addValueEdge (xID, yID, i) m

-- --------------------------------------------------------------- [ Intention ]
||| Perform the insertion of label into the model.
private
insertIntention : GrlIR INTENT -> GModel -> GModel
insertIntention l@(IntentLink ty val x y) model =
  insertLink y x (Just $ convExpr l) model

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
insertStructure l@(StructureLink ty x ys) model =
    updateGoalNode (\n => getIrTitle x == gTitle n)
                   (\x => record {dTy = ty} x)
                   (model' model l)
  where
    model' : GModel -> GrlIR STRUCT -> GModel
    model' mo l = foldl (\m, y => insertLink x y (Just $ convExpr l) m) mo ys


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

infixl 3 \=

(\=) : GRL expr => {ty : GrlIRTy} -> GModel -> expr ty -> GModel
(\=) {ty} m i =
  case ty of
    ELEM   => (\+\)  m i
    INTENT => (\->\) m i
    STRUCT => (\<-\) m i

-- --------------------------------------------------------------------- [ EOF ]
