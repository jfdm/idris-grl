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

import public Decidable.Equality

import Effects
import Effect.State

import public Data.AVL.Graph
import public Data.List
import public Data.Stack

import GRL.Model
import GRL.IR
import GRL.Common

%access public
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

||| The effects used in a BFS.
private
SEffs : List EFFECT
SEffs = [ 'next ::: STATE (Stack NodeID)
        , 'seen ::: STATE (List NodeID)
        , 'res  ::: STATE Bool]

private
partial
doComputeSpan : NodeID -> GModel -> Eff () SEffs
doComputeSpan id g = do
  s <- 'next :- get
  case popS' s of
    Nothing           => pure ()
    Just (curr, newS) => do
      'next :- put newS
      ss <- 'seen :- get
      case elem curr ss || curr == id || elem id ss of
        True => do  -- If encountered cycle
          'res :- put False
          pure ()
        False => do  -- If no cycle
          let cs' = getEdgesByID curr g
          let cs  = filter (\(y,l) => isDeCompEdge l) cs'
          case isNil cs of
            True => do -- If No Children
              'res :- update (\x => x && True)
              doComputeSpan id g
            False => do
              case lookup id cs of
                Just _ => do -- If thing is in children
                  'res :- put False
                  pure ()
                Nothing => do -- if keep on searching
                  let cIDs = map fst cs
                  'seen :- update (\xs => [curr] ++ xs )
                  'next :- update (\xs => xs ++ cIDs)
                  'res :- update (\x => x && True)
                  doComputeSpan id g

%assert_total
computeSpan : GExpr STRUCT -> GModel -> Bool
computeSpan (SLink ty (Elem ty' t s) ds) m =
    runSpan initID ds'
  where
    initID : Maybe NodeID
    initID = getGoalIDByTitle t m

    ds' : List (NodeID)
    ds' = catMaybes $ map (\x => getGoalIDByTitle (getTitle x) m) ds

    runSpan : Maybe NodeID -> List (NodeID) -> Bool
    runSpan Nothing   _  = False
    runSpan (Just id) is = with Effects
      runPureInit [ 'next := pushSThings is mkStack
                  , 'seen := List.Nil
                  , 'res  := True] $ do
        doComputeSpan id m
        r <- 'res :- get
        pure r


%hint
checkStructBool : GExpr STRUCT -> GModel -> Bool
checkStructBool l@(SLink ty src ds) m =
    length ds >= 1
    && allDiff src ds
    && validNodes (src :: ds) m
    && validDTy src ty m
    && computeSpan l m

-- --------------------------------------------------------------------- [ EOF ]
