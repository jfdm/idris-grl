module GRL.Property.Structure

import public Decidable.Equality

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

import public GRL.Property.Common

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

-- --------------------------------------------------------------------- [ EOF ]
