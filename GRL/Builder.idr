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
insertElem : GRL ex => (e : ex ELEM)
                    -> (m : GModel)
                    -> {auto prf : checkElemBool (mkGoal e) m = True}
                    -> GModel
insertElem elem model = addNode (convExpr $ mkGoal elem) model

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
insertIntent : GRL ex => (i : ex INTENT)
                      -> (m : GModel)
                      -> {auto prf : checkIntentBool (mkIntent i) m = True}
                      -> GModel
insertIntent l@(IntentLink ty val x y) model =
  insertLink y x (Just $ (convExpr . mkIntent) l) model

-- --------------------------------------------------------------- [ Structure ]
||| Do structure insertion.
private
insertStruct : GRL ex => (s : ex STRUCT)
                      -> (m : GModel)
                      -> {auto prf : checkStructBool (mkStruct s) m = True}
                      -> GModel
insertStruct l@(StructureLink ty x ys) model =
    updateGoalNode (\n => getIrTitle x == gTitle n)
                   (\x => record {dTy = ty} x)
                   (model' model l)
  where
    model' : GModel -> GrlIR STRUCT -> GModel
    model' mo l = foldl (\m, y => insertLink x y (Just $ (convExpr . mkStruct) l) m) mo ys

infixl 3 \=

(\=) : GRL expr => {ty : GrlIRTy} -> GModel -> expr ty -> GModel
(\=) {ty} m i =
  case ty of
    ELEM   => insertElem i m
    INTENT => insertIntent i m
    STRUCT => insertStruct i m

-- --------------------------------------------------------------------- [ EOF ]
