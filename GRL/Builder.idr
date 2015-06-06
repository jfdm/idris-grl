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
data ValidInsert : {ty : GrlIRTy} -> GrlIR ty -> GModel -> Type where
  IsValidInsert : ValidInsert decl model

||| Perform the insertion of elements into the model.
private
insertElem : GRL ex => (e : ex ELEM)
                    -> (m : GModel)
                    -> (prf : ValidInsert (mkGoal e) m)
                    -> GModel
insertElem elem model p = addNode (convExpr $ mkGoal elem) model

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
                      -> (prf : ValidInsert (mkIntent i) m)
                      -> GModel
insertIntent l@(IntentLink ty val x y) model p =
  insertLink y x (Just $ (convExpr . mkIntent) l) model

-- --------------------------------------------------------------- [ Structure ]
||| Do structure insertion.
private
insertStruct : GRL ex => (s : ex STRUCT)
                      -> (m : GModel)
                      -> (prf : ValidInsert (mkStruct s) m)
                      -> GModel
insertStruct l@(StructureLink ty x ys) model p =
    updateGoalNode (\n => getIrTitle x == gTitle n)
                   (\x => record {dTy = ty} x)
                   (doInsert l model)
  where
    doInsert : GrlIR STRUCT -> GModel -> GModel
    doInsert l mo = foldl (\m, y => insertLink x y (Just $ (convExpr . mkStruct) l) m) mo ys

wildMk : GRL ex => {ty : GrlIRTy}
                -> (e : ex ty)
                -> GrlIR ty
wildMk {ty} decl =
    case ty of
      ELEM   => mkGoal decl
      INTENT => mkIntent decl
      STRUCT => mkStruct decl

public
checkAdd : GRL ex => {ty : GrlIRTy}
                  -> (e : ex ty)
                  -> (m : GModel)
                  -> Maybe (ValidInsert (wildMk e) m)
checkAdd el mo {ty} =
  case ty of
    ELEM   => if checkElemBool (mkGoal el) mo
                then (Just IsValidInsert)
                else Nothing
    INTENT => if checkIntentBool (mkIntent el) mo
                then (Just IsValidInsert)
                else Nothing
    STRUCT => if checkStructBool (mkStruct el) mo
                then (Just IsValidInsert)
                else Nothing

infixl 4 \=

(\=) : GRL expr => {ty : GrlIRTy}
                -> (m : GModel)
                -> (d : expr ty)
                -> {res : ValidInsert (wildMk d) m}
                -> {auto prf : checkAdd d m = Just res}
                -> GModel
(\=) {ty} mod dec {res} =
    case ty of
      ELEM   => insertElem   dec mod res
      INTENT => insertIntent dec mod res
      STRUCT => insertStruct dec mod res

-- --------------------------------------------------------------------- [ EOF ]
