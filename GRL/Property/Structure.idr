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
allDiff : (src : GrlIR ELEM)
       -> (ds  : List (GrlIR ELEM))
       -> Bool
allDiff src ds = diffDSTs && noLoopBack
  where
    diffDSTs : Bool
    diffDSTs = if length ds == 1
                 then True
                 else not $ and [ eqGrlIR x y | x <- ds, y <- ds]

    noLoopBack : Bool
    noLoopBack = not $ and $ map (\x => eqGrlIR x src) ds

||| Nodes are all valid nodes
validNodes : List (GrlIR ELEM)
          -> GModel
          -> Bool
validNodes ns m = and $ map (\n => isValid n m) ns
  where
    isValid : GrlIR ELEM -> GModel -> Bool
    isValid (Element ty t s) m = hasGoal t m

||| The node is free to be decomposed, or has been decomposed and are
||| adding the same decomposition.
validDTy : GrlIR ELEM -> Decomposition -> GModel -> Bool
validDTy (Element ty t s) dty m =
  case getGoalByTitle t m of
    Nothing => True
    Just n  => case dTy n of
      NOTTy => True
      a     => a == dty

%hint
checkStructBool : (link : GrlIR STRUCT)
               -> (model : GModel)
               -> Bool
checkStructBool (StructureLink ty src ds) m =
       allDiff src ds
    && validNodes (src :: ds) m
    && validDTy src ty m

-- --------------------------------------------------------------------- [ EOF ]
