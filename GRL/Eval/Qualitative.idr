-- --------------------------------------------------------- [ Qualitative.idr ]
-- Module    : Qualitative.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Qualitative evaluations for
module GRL.Eval.Qualitative

import GRL.Common
import GRL.Model

%access public

instance [andSN] Cast SValue Nat where
  cast DENIED    = cast 0
  cast CONFLICT  = cast 1
  cast UNDECIDED = cast 1
  cast WEAKDEN   = cast 2
  cast NONE      = cast 3
  cast WEAKSATIS = cast 4
  cast SATISFIED = cast 5

instance [andNS] Cast Nat SValue where
  cast Z                     = DENIED
  cast (S Z)                 = UNDECIDED
  cast (S (S Z))             = WEAKDEN
  cast (S (S (S Z)))         = NONE
  cast (S (S (S (S Z))))     = WEAKSATIS
  cast (S (S (S (S (S Z))))) = SATISFIED
  cast _                     = UNDECIDED


||| Calculate AND decomposition
getDecompAnd : List SValue -> SValue
getDecompAnd ss = cast @{andNS} $ foldl (\olds,s => min (toNat s) olds) (cast 5) ss
  where
    toNat : SValue -> Nat
    toNat sv = cast @{andSN} sv

instance [orSN] Cast SValue Nat where
  cast DENIED    = cast 0
  cast WEAKDEN   = cast 1
  cast NONE      = cast 2
  cast WEAKSATIS = cast 3
  cast CONFLICT  = cast 4
  cast UNDECIDED = cast 4
  cast SATISFIED = cast 5

instance [orNS] Cast Nat SValue where
  cast Z                     = DENIED
  cast (S Z)                 = WEAKDEN
  cast (S (S Z))             = NONE
  cast (S (S (S Z)))         = WEAKSATIS
  cast (S (S (S (S Z))))     = UNDECIDED
  cast (S (S (S (S (S Z))))) = SATISFIED
  cast _                     = UNDECIDED


||| Calculate IOR decomposition.
getDecompIOR : List SValue -> SValue
getDecompIOR ss = cast @{orNS} $ foldl (\olds,s => max (toNat s) olds) (cast 0) ss
  where
    toNat : SValue -> Nat
    toNat sv = cast @{orSN} sv

||| Calculate XOR decomposition.
getDecompXOR : List SValue -> SValue
getDecompXOR ss = cast @{orNS} $ foldl (\olds,s => min (toNat s) olds) (cast 5) ss
  where
    toNat : SValue -> Nat
    toNat sv = cast @{orSN} sv

||| Record to keep track of contribution valeu counts.
record ContribCount where
  constructor MkCCount
  noSatis  : Nat
  noWeakS  : Nat
  noWeakD  : Nat
  noDenied : Nat
  noUndec  : Nat

||| Default constructor for `ContribCount`
defCCount : ContribCount
defCCount = MkCCount Z Z Z Z Z

||| Implementation of `AdjustContributionCounters`
adJustCount : SValue -> ContribCount -> ContribCount
adJustCount SATISFIED cnt = record {noSatis  = (S (noSatis cnt))} cnt
adJustCount DENIED    cnt = record {noDenied = (S (noDenied cnt))} cnt
adJustCount WEAKSATIS cnt = record {noWeakS  = (S (noWeakS cnt))} cnt
adJustCount WEAKDEN   cnt = record {noWeakD  = (S (noWeakD cnt))} cnt
adJustCount UNDECIDED cnt = record {noUndec  = (S (noUndec cnt))} cnt
adJustCount _         cnt = cnt

||| Implementation of `AdjustContributionCounters` for a list of values.
adjustCounts : List SValue -> ContribCount
adjustCounts es = foldl (flip $ adJustCount) defCCount es


||| Implementation of the `WeightedContribution` look up table.
weightedContrib : SValue -> CValue -> SValue
weightedContrib x y = foldl (\res,(x',y',r') => if x == x' && y == y' then r' else res) NONE table
  where
    table : List (SValue, CValue, SValue)
    table = [ (DENIED   , MAKES  ,  DENIED   )
            , (DENIED   , HELPS  ,  WEAKDEN  )
            , (DENIED   , SOMEPOS,  WEAKDEN  )
            , (DENIED   , UNKNOWN,  NONE     )
            , (DENIED   , SOMENEG,  WEAKSATIS)
            , (DENIED   , HURTS  ,  WEAKSATIS)
            , (DENIED   , BREAK  ,  SATISFIED)
            , (WEAKDEN  , MAKES  ,  WEAKDEN  )
            , (WEAKDEN  , HELPS  ,  WEAKDEN  )
            , (WEAKDEN  , SOMEPOS,  WEAKDEN  )
            , (WEAKDEN  , UNKNOWN,  NONE     )
            , (WEAKDEN  , SOMENEG,  WEAKSATIS)
            , (WEAKDEN  , HURTS  ,  WEAKSATIS)
            , (WEAKDEN  , BREAK  ,  WEAKSATIS)
            , (WEAKSATIS, MAKES  ,  WEAKSATIS)
            , (WEAKSATIS, HELPS  ,  WEAKSATIS)
            , (WEAKSATIS, SOMEPOS,  WEAKSATIS)
            , (WEAKSATIS, UNKNOWN,  NONE     )
            , (WEAKSATIS, SOMENEG,  WEAKDEN  )
            , (WEAKSATIS, HURTS  ,  WEAKDEN  )
            , (WEAKSATIS, BREAK  ,  WEAKDEN  )
            , (SATISFIED, MAKES  ,  SATISFIED)
            , (SATISFIED, HELPS  ,  WEAKSATIS)
            , (SATISFIED, SOMEPOS,  WEAKSATIS)
            , (SATISFIED, UNKNOWN,  NONE     )
            , (SATISFIED, SOMENEG,  WEAKDEN  )
            , (SATISFIED, HURTS  ,  WEAKDEN  )
            , (SATISFIED, BREAK  ,  DENIED   )
            , (CONFLICT , MAKES  ,  UNDECIDED)
            , (CONFLICT , HELPS  ,  UNDECIDED)
            , (CONFLICT , SOMEPOS,  UNDECIDED)
            , (CONFLICT , UNKNOWN,  UNDECIDED)
            , (CONFLICT , SOMENEG,  UNDECIDED)
            , (CONFLICT , HURTS  ,  UNDECIDED)
            , (CONFLICT , BREAK  ,  UNDECIDED)
            , (UNDECIDED, MAKES  ,  UNDECIDED)
            , (UNDECIDED, HELPS  ,  UNDECIDED)
            , (UNDECIDED, SOMEPOS,  UNDECIDED)
            , (UNDECIDED, UNKNOWN,  UNDECIDED)
            , (UNDECIDED, SOMENEG,  UNDECIDED)
            , (UNDECIDED, HURTS  ,  UNDECIDED)
            , (UNDECIDED, BREAK  ,  UNDECIDED)
            , (NONE     , MAKES  ,  NONE     )
            , (NONE     , HELPS  ,  NONE     )
            , (NONE     , SOMEPOS,  NONE     )
            , (NONE     , UNKNOWN,  NONE     )
            , (NONE     , SOMENEG,  NONE     )
            , (NONE     , HURTS  ,  NONE     )
            , (NONE     , BREAK  ,  NONE     )]

||| Implementation of the `CompareSatisfiedAndDenied`  resolution
cmpSatAndDen : ContribCount -> SValue
cmpSatAndDen cnt =
  if noSatis cnt > 0 && noDenied cnt > 0
    then CONFLICT
    else if noSatis cnt > 0 && noDenied cnt == 0
      then SATISFIED
      else if noDenied cnt > 0 && noSatis cnt == 0
        then DENIED
        else if noSatis cnt == 0 && noDenied cnt == 0
          then NONE
          else NONE

||| Implementation of the `CompareWSandWD` function
cmpWSandWD : ContribCount -> SValue
cmpWSandWD cnt =
  if noWeakS cnt > noWeakD cnt
    then WEAKSATIS
    else if noWeakD cnt > noWeakS cnt
      then WEAKDEN
      else if noWeakD cnt == noWeakS cnt
        then NONE
        else NONE

||| Implementation of the `CombineContributionutions` function
combineContribs : ContribCount -> SValue
combineContribs c = doCombine (cmpWSandWD c) (cmpSatAndDen c)
  where
    table : List (SValue, SValue, SValue)
    table =[ (WEAKDEN  , DENIED   , DENIED   )
           , (WEAKDEN  , SATISFIED, WEAKSATIS)
           , (WEAKDEN  , CONFLICT , CONFLICT )
           , (WEAKDEN  , NONE     , WEAKDEN  )
           , (WEAKSATIS, DENIED   , WEAKDEN  )
           , (WEAKSATIS, SATISFIED, SATISFIED)
           , (WEAKSATIS, CONFLICT , CONFLICT )
           , (WEAKSATIS, NONE     , WEAKSATIS)
           , (NONE     , DENIED   , DENIED   )
           , (NONE     , SATISFIED, SATISFIED)
           , (NONE     , CONFLICT , CONFLICT )
           , (NONE     , NONE     , NONE     )]

    doCombine : SValue -> SValue -> SValue
    doCombine x y = foldl (\res,(x',y',r') => if x == x' && y == y' then r' else res) NONE table

-- --------------------------------------------------------------------- [ EOF ]
