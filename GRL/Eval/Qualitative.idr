-- --------------------------------------------------------- [ Qualitative.idr ]
-- Module    : Qualitative.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Qualitative evaluations for
module GRL.Eval.Qualitative

import public Effects
import public Effect.State
import public Effect.Exception

import GRL.Common
import GRL.Model

%access public

instance [andSN] Cast SValue Nat where
  cast DENIED    = cast 0
  cast CONFLICT  = cast 1
  cast UNKNOWN   = cast 1
  cast WEAKDEN   = cast 2
  cast NONE      = cast 3
  cast WEAKSATIS = cast 4
  cast SATISFIED = cast 5

instance [andNS] Cast Nat SValue where
  cast Z                     = DENIED
  cast (S Z)                 = UNKNOWN
  cast (S (S Z))             = WEAKDEN
  cast (S (S (S Z)))         = NONE
  cast (S (S (S (S Z))))     = WEAKSATIS
  cast (S (S (S (S (S Z))))) = SATISFIED
  cast _                     = UNKNOWN


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
  cast UNKNOWN   = cast 4
  cast SATISFIED = cast 5

instance [orNS] Cast Nat SValue where
  cast Z                     = DENIED
  cast (S Z)                 = WEAKDEN
  cast (S (S Z))             = NONE
  cast (S (S (S Z)))         = WEAKSATIS
  cast (S (S (S (S Z))))     = UNKNOWN
  cast (S (S (S (S (S Z))))) = SATISFIED
  cast _                     = UNKNOWN


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
adJustCount UNKNOWN   cnt = record {noUndec  = (S (noUndec cnt))} cnt
adJustCount _         cnt = cnt

||| Implementation of `AdjustContributionCounters` for a list of values.
adjustCounts : List SValue -> ContribCount
adjustCounts es = foldl (flip $ adJustCount) defCCount es

||| Implementation of the `WeightedContribution` look up table.
weightedContrib : SValue -> CValue -> SValue
weightedContrib  DENIED    MAKE    = DENIED
weightedContrib  DENIED    HELPS   = WEAKDEN
weightedContrib  DENIED    SOMEPOS = WEAKDEN
weightedContrib  DENIED    UNKNOWN    = NONE
weightedContrib  DENIED    SOMENEG = WEAKSATIS
weightedContrib  DENIED    HURT    = WEAKSATIS
weightedContrib  DENIED    BREAK   = SATISFIED
weightedContrib  WEAKDEN   MAKE    = WEAKDEN
weightedContrib  WEAKDEN   HELPS   = WEAKDEN
weightedContrib  WEAKDEN   SOMEPOS = WEAKDEN
weightedContrib  WEAKDEN   UNKNOWN    = NONE
weightedContrib  WEAKDEN   SOMENEG = WEAKSATIS
weightedContrib  WEAKDEN   HURT    = WEAKSATIS
weightedContrib  WEAKDEN   BREAK   = WEAKSATIS
weightedContrib  WEAKSATIS MAKE    = WEAKSATIS
weightedContrib  WEAKSATIS HELPS    = WEAKSATIS
weightedContrib  WEAKSATIS SOMEPOS = WEAKSATIS
weightedContrib  WEAKSATIS UNKNOWN    = NONE
weightedContrib  WEAKSATIS SOMENEG = WEAKDEN
weightedContrib  WEAKSATIS HURT    = WEAKDEN
weightedContrib  WEAKSATIS BREAK   = WEAKDEN
weightedContrib  SATISFIED MAKE    = SATISFIED
weightedContrib  SATISFIED HELPS   = WEAKSATIS
weightedContrib  SATISFIED SOMEPOS = WEAKSATIS
weightedContrib  SATISFIED UNKNOWN    = NONE
weightedContrib  SATISFIED SOMENEG = WEAKDEN
weightedContrib  SATISFIED HURT    = WEAKDEN
weightedContrib  SATISFIED BREAK   = DENIED
weightedContrib  CONFLICT  MAKE    = UNKNOWN
weightedContrib  CONFLICT  HELPS   = UNKNOWN
weightedContrib  CONFLICT  SOMEPOS = UNKNOWN
weightedContrib  CONFLICT  UNKNOWN    = UNKNOWN
weightedContrib  CONFLICT  SOMENEG = UNKNOWN
weightedContrib  CONFLICT  HURT    = UNKNOWN
weightedContrib  CONFLICT  BREAK   = UNKNOWN
weightedContrib  UNKNOWN MAKE    = UNKNOWN
weightedContrib  UNKNOWN HELPS   = UNKNOWN
weightedContrib  UNKNOWN SOMEPOS = UNKNOWN
weightedContrib  UNKNOWN UNKNOWN    = UNKNOWN
weightedContrib  UNKNOWN SOMENEG = UNKNOWN
weightedContrib  UNKNOWN HURT    = UNKNOWN
weightedContrib  UNKNOWN BREAK   = UNKNOWN
weightedContrib  NONE      MAKE    = NONE
weightedContrib  NONE      HELPS   = NONE
weightedContrib  NONE      SOMEPOS = NONE
weightedContrib  NONE      UNKNOWN    = NONE
weightedContrib  NONE      SOMENEG = NONE
weightedContrib  NONE      HURT    = NONE
weightedContrib  NONE      BREAK   = NONE
weightedContrib  _         _       = NONE


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
        else UNKNOWN


{-
  noSatis  : Nat
  noWeakS  : Nat
  noWeakD  : Nat
  noDenied : Nat
  noUndec  : Nat

-}
||| Implementation of the `CombineContributionutions` function
%inline
combineContribs : SValue -> SValue -> SValue
combineContribs WEAKDEN   DENIED    = DENIED
combineContribs WEAKDEN   SATISFIED = WEAKSATIS
combineContribs WEAKDEN   CONFLICT  = CONFLICT
combineContribs WEAKDEN   NONE      = WEAKDEN
combineContribs WEAKSATIS DENIED    = WEAKDEN
combineContribs WEAKSATIS SATISFIED = SATISFIED
combineContribs WEAKSATIS CONFLICT  = CONFLICT
combineContribs WEAKSATIS NONE      = WEAKSATIS
combineContribs NONE      DENIED    = DENIED
combineContribs NONE      SATISFIED = SATISFIED
combineContribs NONE      CONFLICT  = CONFLICT
combineContribs NONE      NONE      = NONE
combineContribs _         _         = UNKNOWN

-- --------------------------------------------------------------------- [ EOF ]
