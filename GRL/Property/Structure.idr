||| This section details the check for structural link insertion.
|||
||| Correctness/Soundess Properties of a Structural Link
|||
||| 1. The src and destination must not be the same.
||| 2. A node can only be decomposed once.
|||   1. The link must be valid for the parent.
|||   2.
||| 3. A parent cannot be contained by its children.
|||
module GRL.Property.Structure

import public Decidable.Equality

import public Data.AVL.Set
import public Data.AVL.Graph
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

-- ----------------------------------------------- [ Structural Link Insertion ]

allDiff : (src : GRLExpr ELEM)
       -> (ds  : List (GRLExpr ELEM))
       -> Bool
allDiff src ds = diffDSTs && noLoopBack
  where
    diffDSTs : Bool
    diffDSTs = not $ and [ eqGRLExpr x y | x <- ds, y <- ds]

    noLoopBack : Bool
    noLoopBack = not $ and $ map (\x => eqGRLExpr x src) ds

validNodes : List (GRLExpr ELEM)
          -> GModel
          -> Bool
validNodes ns m = and $ map (\n => isValid n m) ns
  where
    isValid : GRLExpr ELEM -> GModel -> Bool
    isValid (Element ty t s) m = hasGoal t m

validDTy : GRLExpr ELEM -> GModel -> Bool
validDTy (Element ty t s) m = True

validLink : GRLExpr ELEM -> List (GRLExpr ELEM) -> GModel -> Bool
validLink sec ds m = True

%hint
checkStructBool : (link : GRLExpr STRUCT)
               -> (model : GModel)
               -> Bool
checkStructBool (StructureLink ty src ds) m =
       allDiff src ds
    && validNodes (src :: ds) m
    && validDTy src m
    && validLink src ds m

-- --------------------------------------------------------------------- [ EOF ]
