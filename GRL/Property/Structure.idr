-- ----------------------------------------------------------- [ Structure.idr ]
-- Module    : Structure.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

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

import public Data.AVL.Graph
import public Data.List
import public Data.Stack

import GRL.Model
import GRL.IR
import GRL.Common

%default partial
%access export

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
    Nothing => False
    Just n  => case getStructTy n of
        Nothing  => True
        Just xty => xty == dty


-- -------------------------------------------------------------- [ Evaluation ]
private
record ComputeState where
  constructor MkState
  next : Stack NodeID
  seen : List NodeID

private
defState : List NodeID -> ComputeState
defState is = MkState (pushSThings is mkStack) (List.Nil)

private
cycleCheck : NodeID -> NodeID -> List NodeID -> Bool
cycleCheck id curr seen = elem curr seen || curr == id || elem id seen

partial
private
doComputeSpan : (id    : NodeID)
              -> (model : GModel)
              -> (st    : ComputeState)
              -> Bool
doComputeSpan id g st =
    case popS' (next st) of
      Nothing          => True
      Just (curr, newS) =>  -- TODO
        if cycleCheck id curr (seen st)
          then False
          else let cs = children curr in
              if isNil cs
                then True && doComputeSpan id g
                                 (record { next = newS} st)
                else
                  if elem id cs
                    then False -- If thing is in children
                    else True && doComputeSpan id g
                        (record { seen = curr :: (seen st)
                                , next = newS ++ cs} st)
  where
    children : NodeID -> List NodeID
    children n = map fst $ getDeCompEdges n g


%assert_total
computeSpan : GExpr STRUCT -> GModel -> Bool
computeSpan (SLink ty (Elem ty' t s) ds) m =
    case initID of
      Nothing => False
      Just id => doComputeSpan id m (defState ds')
  where
    initID : Maybe NodeID
    initID = getGoalIDByTitle t m

    ds' : List (NodeID)
    ds' = catMaybes $ map (\x => getGoalIDByTitle (getTitle x) m) ds

partial
checkStructBool : GExpr STRUCT -> GModel -> Bool
checkStructBool l@(SLink ty src ds) m =
    length ds >= 1
    && allDiff src ds
    && validNodes (src :: ds) m
    && validDTy src ty m
    && computeSpan l m

-- --------------------------------------------------------------------- [ EOF ]
