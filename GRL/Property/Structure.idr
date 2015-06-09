||| This section details the check for structural link insertion.
|||
||| Correctness/Soundess Properties of a Structural Link
|||
||| 1. The src and destination must not be the same.
||| 2. A node can only be decomposed once.
||| 3. The decomposition type must be valid for the parent.
||| 4. A parent cannot be contained by its children.
|||
module GRL.Property.Structure

import public Decidable.Equality

import public Data.AVL.Dependent.Graph
import public Data.List

import GRL.Model
import GRL.IR
import GRL.Common

-- ----------------------------------------------- [ Structural Link Insertion ]

||| No loops and all different children.
allDiff : GExpr ELEM -> List (GExpr ELEM) -> Bool
allDiff src ds = diffDSTs ds && noLoopBack src ds
  where
    diffDSTs : List (GExpr ELEM) -> Bool
    diffDSTs xs = if length xs == 1
                   then True
                   else not $ and [ eqGExpr x y | x <- xs, y <- xs]

    noLoopBack : GExpr ELEM -> List (GExpr ELEM) -> Bool
    noLoopBack y xs = not $ and $ map (\x => eqGExpr x y) xs

||| Nodes are all valid nodes
validNodes : List (GExpr ELEM) -> GModel -> Bool
validNodes ns m = and $ map (\n => isValid n m) ns
  where
    isValid : GExpr ELEM -> GModel -> Bool
    isValid (Elem ty t s) m = hasGoal t m

||| The node is free to be decomposed, or has been decomposed and are
||| adding the same decomposition.
validDTy : GExpr ELEM -> GStructTy -> GModel -> Bool
validDTy (Elem ty t s) dty m =
  case getGoalByTitle t m of
    Nothing => True
    Just n  => getStructTy n == Just dty

%hint
checkStructBool : GExpr STRUCT -> GModel -> Bool
checkStructBool (SLink ty src ds) m =
       allDiff src ds
    && validNodes (src :: ds) m
    && validDTy src ty m

-- --------------------------------------------------------------------- [ EOF ]
