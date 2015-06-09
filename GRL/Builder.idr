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

import Debug.Error

%access public

-- ---------------------------------------------------- [ Allowed Constructors ]

||| Create an empty model
emptyModel : GModel
emptyModel = mkEmptyGraph

-- ------------------------------------------------------------- [ Interpreter ]

|||  Interpt the IR types to get Goal Graph Types.
interpTy : GTy -> Type
interpTy ELEM   = GoalNode
interpTy INTENT = GoalEdge
interpTy STRUCT = GoalEdge

||| Convert expressions from the IR to Goal Graph objects.
convExpr : {ty : GTy} -> GExpr ty -> interpTy ty
convExpr (Elem eTy t s)            = GNode eTy t s Nothing
convExpr (ILink IMPACTSty cTy _ _) = Contribution cTy
convExpr (ILink AFFECTSty cTy _ _) = Correlation  cTy
convExpr (SLink _ _ _) = Decomp

-- --------------------------------------------------------------- [ Insertion ]
data ValidInsert : {ty : GTy} -> GExpr ty -> GModel -> Type where
  IsValidInsert : ValidInsert decl model

||| Perform the insertion of elements into the model.
private
insertElem : GRL expr => (e : expr ELEM)
                      -> (m : GModel)
                      -> ValidInsert (mkGoal e) m
                      -> GModel
insertElem elem model p = addNode (convExpr $ mkGoal elem) model

-- ------------------------------------------------------------------- [ Links ]
private
insertLink : GExpr ELEM -> GExpr ELEM -> Maybe GoalEdge -> GModel -> GModel
insertLink (Elem _ x _) (Elem _ y _) i m =
  case getGoalByTitle x m of
    Nothing  => m
    Just xID =>
      case getGoalByTitle y m of
        Nothing  => m
        Just yID => addValueEdge (xID, yID, i) m

-- --------------------------------------------------------------- [ Intention ]
||| Perform the insertion of label into the model.
private
insertIntent : GRL expr => (i : expr INTENT)
                        -> (m : GModel)
                        -> ValidInsert (mkIntent i) m
                        -> GModel
insertIntent l@(ILink ty val x y) model p =
  insertLink y x (Just $ (convExpr . mkIntent) l) model

-- --------------------------------------------------------------- [ Structure ]
||| Do structure insertion.
private
insertStruct : GRL expr => (s : expr STRUCT)
                        -> (m : GModel)
                        -> ValidInsert (mkStruct s) m
                        -> GModel
insertStruct l@(SLink ty x ys) model p =
    updateGoalNode (\n => getTitle x == getNodeTitle n)
                   (\x => record {getStructTy = Just ty} x)
                   (doInsert l model)
  where
    doInsert : GExpr STRUCT -> GModel -> GModel
    doInsert l mo = foldl (\m, y => insertLink x y (Just $ (convExpr . mkStruct) l) m) mo ys

wildMk : GRL expr => {ty : GTy}
                  -> (expr ty)
                  -> GExpr ty
wildMk {ty=ELEM}   decl = mkGoal decl
wildMk {ty=INTENT} decl = mkIntent decl
wildMk {ty=STRUCT} decl = mkStruct decl

insert : GRL expr => {ty : GTy}
                  -> expr ty
                  -> GModel
                  -> GModel
insert {ty=ELEM} decl model =
    if checkElemBool (mkGoal decl) model
      then (insertElem decl model IsValidInsert)
      else error "Bad Element"

insert {ty=INTENT} decl model =
    if checkIntentBool (mkIntent decl) model
      then (insertIntent decl model IsValidInsert)
      else error "Bad Intent"

insert {ty=STRUCT} decl model =
    if checkStructBool (mkStruct decl) model
      then (insertStruct decl model IsValidInsert)
      else error "Bad Structure"


infixl 4 \=

(\=) : GRL expr => {ty : GTy}
                -> (m : GModel)
                -> (d : expr ty)
                -> GModel
(\=) model decl = insert decl model

-- ------------------------------------------------------------- [ Applicative ]
-- This allows use of idiom brackets.


(<*>) : GRL expr => {ty : GTy}
                  -> GModel
                  -> (d : expr ty)
                  -> GModel
(<*>) m a = m \= a

pure : GModel -> GModel
pure a = a

-- ------------------------------------------------------------- [ Do Notation ]
-- This should allow for do notation to be employed...

data GExpr : Type where
  Decl : GRL expr => {ty : GTy}
                  -> expr ty
                  -> GExpr
  Seq : GExpr -> GExpr -> GExpr

(>>=) : GExpr -> (() -> GExpr) -> GExpr
(>>=) first andThen = Seq first (andThen ())

implicit
convDecl : GRL expr => {ty : GTy}
                    -> (expr ty)
                    -> GExpr
convDecl = Decl

mkModel : GModel -> GExpr -> GModel
mkModel m (Decl e)  = m \= e
mkModel m (Seq a b) = mkModel (mkModel m a) b


-- --------------------------------------------------------------------- [ EOF ]
