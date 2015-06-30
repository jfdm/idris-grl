||| This module defines a 'compiler' that transforms the GRL IR into the Goal Graph.
module GRL.Builder

import public Data.AVL.Graph
import public Data.Sigma.DList
import public Data.List

import GRL.Model
import GRL.IR
import GRL.Common
import GRL.Property.Element
import GRL.Property.Intention
import GRL.Property.Structure
import GRL.Pretty

import Debug.Error
import Debug.Trace

%access public
%default total
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
convExpr (SLink _ _ _)             = Decomp

-- --------------------------------------------------------------- [ Insertion ]
data ValidInsert : {ty : GTy} -> GExpr ty -> GModel -> Type where
  IsValidInsert : ValidInsert decl model

||| Perform the insertion of elements into the model.
private
insertElem : (e : GExpr ELEM)
          -> (m : GModel)
          -> ValidInsert e m
          -> GModel
insertElem el model p = addNode (convExpr el) model

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
insertIntent : (i : GExpr INTENT)
            -> (m : GModel)
            -> ValidInsert i m
            -> GModel
insertIntent (ILink ty val x y) model p =
  insertLink y x (Just (convExpr (ILink ty val x y))) model

-- --------------------------------------------------------------- [ Structure ]
||| Do structure insertion.
private
insertStruct : (s : GExpr STRUCT)
            -> (m : GModel)
            -> ValidInsert s m
            -> GModel
insertStruct (SLink ty x ys) model p =
    updateGoalNode (\n => getTitle x == getNodeTitle n)
                   (\n => record {getStructTy = Just ty} n)
                   model'
  where
    model' : GModel
    model' = foldl (\m, y => insertLink x y (Just $ (convExpr (SLink ty x ys))) m)
                   model ys

wildMk : GRL expr => {ty : GTy}
                  -> (expr ty)
                  -> GExpr ty
wildMk {ty=ELEM}   decl = mkGoal decl
wildMk {ty=INTENT} decl = mkIntent decl
wildMk {ty=STRUCT} decl = mkStruct decl

insert : GRL expr => expr ty
                  -> GModel
                  -> GModel
insert {ty=ELEM} decl model =
    if checkElemBool (mkGoal decl) model
      then (insertElem (mkGoal decl) model IsValidInsert)
      else error $ with List unwords ["Bad Element arises from trying to insert\n\n\t", show (mkGoal decl), "\n\ninto\n\n\t", prettyModel model]

insert {ty=INTENT} decl model =
    if checkIntentBool (mkIntent decl) model
      then (insertIntent (mkIntent decl) model IsValidInsert)
      else error $ with List unwords ["Bad Intent arises from trying to insert\n\n\t", show (mkIntent decl), "\n\ninto\n\n\t", prettyModel model]

insert {ty=STRUCT} decl model =
    if checkStructBool (mkStruct decl) model
      then (insertStruct (mkStruct decl) model IsValidInsert)
      else error $ with List unwords ["Bad Structure arises from trying to insert\n\n\t", show (mkStruct decl), "\n\ninto\n\n\t",prettyModel model]

insertMany : GRL expr => List (expr ty)
                      -> GModel
                      -> GModel
insertMany Nil model = model
insertMany ds model = with List foldl (flip $ insert) model ds

insertMany' : GRL expr => DList GTy expr ts
                       -> GModel
                       -> GModel
insertMany' Nil model = model
insertMany' ds model = with DList foldl (flip $ insert) model ds

infixl 4 \=

(\=) : GRL expr => (m : GModel)
                -> (d : expr ty)
                -> GModel
(\=) model decl = insert decl model

{-
-- ------------------------------------------------------------- [ Applicative ]
-- This allows use of idiom brackets.

partial
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

partial
mkModel : GModel -> GExpr -> GModel
mkModel m (Decl e)  = m \= e
mkModel m (Seq a b) = mkModel (mkModel m a) b
-}
-- --------------------------------------------------------------------- [ EOF ]
