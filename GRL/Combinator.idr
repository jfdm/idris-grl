 module GRL.Combinator

import public Decidable.Equality

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.SigmaList
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

%access public

-- ---------------------------------------------------- [ Allowed Constructors ]
emptyModel : GModel
emptyModel = MkModel Z Empty

-- --------------------------------------------------- [ Valid Insertion Proof ]
||| Predicate to denote valid insertion of an item into the model.
data ValidInsert : (ty : GRLExprTy)
                -> GRLExpr ty
                -> GModel
                -> Type
  where
    ElemInsert   : ValidInsert ELEM i m
    IntentInsert : ValidInsert INTENT i m
    StructInsert : ValidInsert STRUCT i m

-- ------------------------------------------------------- [ Element Insertion ]

||| This section details the property checks for element insertion.
|||
||| Correctness/Soundness Properties ::
|||
||| 1. All elements added to the model must be unique.
|||
||| Note ::
|||
||| + This property should probably be replaced within the model using a Set.
|||
checkElem : (i : GRLExpr ELEM)
         -> (m : GModel)
         -> Dec (ValidInsert ELEM i m)
checkElem (Element ty t s) m =
  case (hasGoal t m) of
     Nothing => Yes (ElemInsert)
     Just n  => No  (believe_me)

-- ----------------------------------------------- [ Structural Link Insertion ]
-- This section details the check for structural link insertion.
--

-- data ValidStruc : (GModel ELEM)
--                -> List (GModel ELEM)
--                -> GModel MODEL
--                -> Type
--   where
--     ValidStrucLink : ValidStruc src dsts model

-- Correctness/Soundess Properties of a Structural Link
--
-- 1. The src and destination must not be the same.
-- 2. A node can only be decomposed once.
--   1. The link must be valid for the parent.
--   2.
-- 3. A parent cannot be contained by its children.

||| The Decomposition proposed is valid.
data ValidDeComp : (src : GRLExpr ELEM)
                -> (ty : DecompTy)
                -> Type
  where
    SameDeCompTy : ValidDeComp src ty
    SetDeCompTy  : ValidDeComp src ty

private
checkStructTy : (src : GModel ELEM)
             -> (ty : DecompTy)
             -> Dec (ValidDeComp src ty)
checkStructTy src ty =
  case (getElemDTy src) of
    Nothing  => Yes (SetDeCompTy)
    Just ty' => case ty' == ty of
      True  => Yes (SameDeCompTy)
      False => No  (believe_me)

private
doCheckStruc : (sTy : DecompTy)
            -> (src : GModel ELEM)
            -> (dests : List (GModel ELEM))
            -> (model : GModel MODEL)
            -> Dec (ValidStruc src dests model)
doCheckStruc ty src dests (GRLSpec es _ ss) with (List.isElem src dests) -- (Check 1)
    | Yes con = No (believe_me)
    | No  prf with (checkStructTy src ty)
      | No  con' = No (believe_me)
      | Yes prf' = Yes (ValidStrucLink)



private
checkStruc : (item : GModel SLINK)
          -> (model : GModel MODEL)
          -> Dec (ValidInsert SLINK item model)
checkStruc (AND x xs) model with (doCheckStruc ANDTy x xs model)
    | Yes prf = Yes (StructInsert)
    | No  con = No (believe_me)
checkStruc (IOR x xs) model with (doCheckStruc IORTy x xs model)
    | Yes prf = Yes (StructInsert)
    | No  con = No (believe_me)
checkStruc (XOR x xs) model with (doCheckStruc XORTy x xs model)
    | Yes prf = Yes (StructInsert)
    | No  con = No (believe_me)

-- ---------------------------------------------- [ Intentional Link Insertion ]

-- This section details the combinator for intentional link insertion.
--
-- Correctness/Soundness Properties of an Intentional Link
--
-- 1. The link should use elements that are in the model.
-- 2. The destination cannot have type: Resource
-- 3. The src and destination must not be the same.


-- -------------------------------------------------------- [ Group the Checks ]
checkInsert : (i : GRLExpr ty)
           -> (m : GModel)
           -> Dec (ValidInsert ty i m)
checkInsert {ty=ELEM}   e m = (checkElem e m)
checkInsert {ty=INTENT} e m = Yes (IntentInsert)
checkInsert {ty=STRUCT} e m = Yes (StructInsert)


-- --------------------------------------------------------------- [ Insertion ]
mkGoalNode : GRLExpr ELEM -> GoalNode
mkGoalNode (Element ety t s) =
  case ety of
    GOAL => Goal t s Nothing
    SOFT => Soft t s Nothing
    TASK => Task t s Nothing
    RES  => Res  t s Nothing

private
insert : (item : GRLExpr ty)
      -> (model : GModel)
      -> (prf : ValidInsert ty item model)
      -> GModel
insert {ty=ELEM}   e (MkModel c m) prf = MkModel (S c) (addNode (c, mkGoalNode e) m)
insert {ty=INTENT} i (MkModel c m) prf = MkModel c m
insert {ty=STRUCT} s (MkModel c m) prf = MkModel c m

infixl 4 /+/

(/+/) : (model : GModel)
     -> (item : GRLExpr ty)
     -> {auto prf : ValidInsert ty item model}
     -> GModel
(/+/) m i {prf} = insert i m prf

-- ---------------------------------------------------------- [ Combine Models ]
-- private
-- insertModel : GModel MODEL
--            -> GModel MODEL
--            -> GModel MODEL
-- insertModel (GRLSpec xs ys zs) g =
--   let g'  = foldr (\e, m => insertElem e m) g xs   in
 --   let g'' = foldr (insertILink) g' ys in
--       foldr insertSLink g'' zs


-- --------------------------------------------------------------------- [ EOF ]
