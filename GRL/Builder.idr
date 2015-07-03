-- ------------------------------------------------------------- [ Builder.idr ]
-- Module    : Builder.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| This module defines an 'interpreter' for constructing Goal Graphs
||| from GRL esque languages.
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
--          -> ValidInsert e m
          -> GModel
insertElem decl model =
  if not $ checkElemBool decl model
    then error $ with List unwords
            ["Bad Element arises from trying to insert\n\n\t"
            , show decl
            , "\n\ninto\n\n\t"
            , prettyModel model]
    else addNode (convExpr decl) model

-- ------------------------------------------------------------------- [ Links ]

||| Do the actual insertion of an edge into the model.
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
--            -> ValidInsert i m
            -> GModel
insertIntent decl@(ILink ty val x y) model =
  if not $ checkIntentBool decl model
      then error $ with List unwords
             ["Bad Intent arises from trying to insert\n\n\t"
             , show decl
             , "\n\ninto\n\n\t"
             , prettyModel model]
      else insertLink y x (Just (convExpr decl)) model

-- --------------------------------------------------------------- [ Structure ]
||| Do structure insertion.
private
insertStruct : (s : GExpr STRUCT)
            -> (m : GModel)
--            -> ValidInsert s m
            -> GModel
insertStruct decl@(SLink ty x ys) model =
    if not $ checkStructBool decl model
      then error $ with List unwords
             ["Bad Structure arises from trying to insert\n\n\t"
             , show decl
             , "\n\ninto\n\n\t",
             prettyModel model]
      else newModel
  where
    model' : GModel
    model' = foldl (\m, y => insertLink x y (Just $ (convExpr (SLink ty x ys))) m)
                   model ys

    newModel : GModel
    newModel = updateGoalNode (\n => getTitle x == getNodeTitle n)
                   (\n => record {getStructTy = Just ty} n)
                   model'

-- ----------------------------------------------------------- [ Do the Insert ]

||| Insert a single declarations into the model.
insert : GRL expr => expr ty
                  -> GModel
                  -> GModel
insert {ty=ELEM}   decl model = insertElem   (mkElem decl)   model
insert {ty=INTENT} decl model = insertIntent (mkIntent decl) model
insert {ty=STRUCT} decl model = insertStruct (mkStruct decl) model

||| Insert many declarations of the same type into the model.
insertMany : GRL expr => List (expr ty)
                      -> GModel
                      -> GModel
insertMany Nil model = model
insertMany ds model = with List foldl (flip $ insert) model ds

||| Insert many different declarations into the model.
insertMany' : GRL expr => DList GTy expr ts
                       -> GModel
                       -> GModel
insertMany' Nil model = model
insertMany' ds model = with DList foldl (flip $ insert) model ds


infixl 4 \=

||| Short hand for inserting a single declaration.
(\=) : GRL expr => (m : GModel)
                -> (d : expr ty)
                -> GModel
(\=) model decl = insert decl model

-- --------------------------------------------------------------------- [ EOF ]
