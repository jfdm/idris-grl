||| Qualitative evaluations for
module GRL.Eval.Qualitative

import public Effects
import public Effect.State
import public Effect.Exception


import GRL.Common
import GRL.Model

%access public

instance [andSat] Ord SValue where
   compare SATISFIED SATISFIED = EQ
   compare WEAKSATIS WEAKSATIS = EQ
   compare WEAKDEN   WEAKDEN   = EQ
   compare DENIED    DENIED    = EQ
   compare CONFLICT  CONFLICT  = EQ
   compare UNKNOWN   UNKNOWN   = EQ
   compare NONE      NONE      = EQ
   compare UNDECIDED UNDECIDED = EQ
   compare DENIED    _         = LT
   compare _         DENIED    = GT
   compare CONFLICT  UNDECIDED = EQ
   compare UNDECIDED CONFLICT  = EQ
   compare CONFLICT  _         = LT
   compare _         CONFLICT  = GT
   compare UNDECIDED _         = LT
   compare _         UNDECIDED = GT
   compare WEAKDEN   _         = LT
   compare _         WEAKDEN   = GT
   compare NONE      _         = LT
   compare _         NONE      = GT
   compare WEAKSATIS _         = LT
   compare _         WEAKSATIS = GT
   compare SATISFIED _         = GT
   compare _         SATISFIED = LT

getDecompAnd : List SValue -> SValue
getDecompAnd ss = foldl (\olds,s => min @{andSat} s olds) SATISFIED ss

instance [orSat] Ord SValue where
    compare SATISFIED SATISFIED = EQ
    compare WEAKSATIS WEAKSATIS = EQ
    compare WEAKDEN   WEAKDEN   = EQ
    compare DENIED    DENIED    = EQ
    compare CONFLICT  CONFLICT  = EQ
    compare UNKNOWN   UNKNOWN   = EQ
    compare NONE      NONE      = EQ
    compare UNDECIDED UNDECIDED = EQ
    compare DENIED    _         = LT
    compare _         DENIED    = GT
    compare WEAKDEN   _         = LT
    compare _         WEAKDEN   = GT
    compare NONE      _         = LT
    compare _         NONE      = GT
    compare WEAKSATIS _         = LT
    compare _         WEAKSATIS = GT
    compare CONFLICT  UNDECIDED = EQ
    compare UNDECIDED CONFLICT  = EQ
    compare CONFLICT  _         = LT
    compare _         CONFLICT  = GT
    compare UNDECIDED _         = LT
    compare _         UNDECIDED = GT
    compare SATISFIED _         = GT
    compare _         SATISFIED = LT

getDecompIOR : List SValue -> SValue
getDecompIOR ss = foldl (\olds,s => min @{orSat} s olds) SATISFIED ss

getDecompXOR : List SValue -> SValue
getDecompXOR ss = foldl (\olds,s => max @{orSat} s olds) DENIED ss

record ContribCount where
  constructor MkCCount
  noSatis  : Nat
  noWeakS  : Nat
  noWeakD  : Nat
  noDenied : Nat
  noUndec  : Nat

defCCount : ContribCount
defCCount = MkCCount Z Z Z Z Z

||| Implementation of `AdjustContributionCounters`
adJustCount : SValue -> ContribCount -> ContribCount
adJustCount SATISFIED cnt = record {noSatis = (S (noSatis cnt))} cnt
adJustCount WEAKSATIS cnt = record {noWeakS = (S (noWeakS cnt))} cnt
adJustCount WEAKDEN   cnt = record {noWeakD = (S (noWeakD cnt))} cnt
adJustCount UNDECIDED cnt = record {noUndec = (S (noUndec cnt))} cnt
adJustCount _         cnt = cnt

||| Implementation of `AdjustContributionCounters` for a list of values.
adjustCounts : List SValue -> ContribCount
adjustCounts es = foldl (flip $ adJustCount) defCCount es

||| Implementation of the `WeightedContribution` look up table.
weightedContrib : SValue -> CValue -> SValue
weightedContrib  DENIED    MAKE    = DENIED
weightedContrib  DENIED    HELPS   = WEAKDEN
weightedContrib  DENIED    SOMEPOS = WEAKDEN
weightedContrib  DENIED    ZERO    = NONE
weightedContrib  DENIED    SOMENEG = WEAKSATIS
weightedContrib  DENIED    HURT    = WEAKSATIS
weightedContrib  DENIED    BREAK   = SATISFIED
weightedContrib  WEAKDEN   MAKE    = WEAKDEN
weightedContrib  WEAKDEN   HELPS   = WEAKDEN
weightedContrib  WEAKDEN   SOMEPOS = WEAKDEN
weightedContrib  WEAKDEN   ZERO    = NONE
weightedContrib  WEAKDEN   SOMENEG = WEAKSATIS
weightedContrib  WEAKDEN   HURT    = WEAKSATIS
weightedContrib  WEAKDEN   BREAK   = WEAKSATIS
weightedContrib  WEAKSATIS MAKE    = WEAKSATIS
weightedContrib  WEAKSATIS HELPS    = WEAKSATIS
weightedContrib  WEAKSATIS SOMEPOS = WEAKSATIS
weightedContrib  WEAKSATIS ZERO    = NONE
weightedContrib  WEAKSATIS SOMENEG = WEAKDEN
weightedContrib  WEAKSATIS HURT    = WEAKDEN
weightedContrib  WEAKSATIS BREAK   = WEAKDEN
weightedContrib  SATISFIED MAKE    = SATISFIED
weightedContrib  SATISFIED HELPS   = WEAKSATIS
weightedContrib  SATISFIED SOMEPOS = WEAKSATIS
weightedContrib  SATISFIED ZERO    = NONE
weightedContrib  SATISFIED SOMENEG = WEAKDEN
weightedContrib  SATISFIED HURT    = WEAKDEN
weightedContrib  SATISFIED BREAK   = DENIED
weightedContrib  CONFLICT  MAKE    = UNDECIDED
weightedContrib  CONFLICT  HELPS   = UNDECIDED
weightedContrib  CONFLICT  SOMEPOS = UNDECIDED
weightedContrib  CONFLICT  ZERO    = UNDECIDED
weightedContrib  CONFLICT  SOMENEG = UNDECIDED
weightedContrib  CONFLICT  HURT    = UNDECIDED
weightedContrib  CONFLICT  BREAK   = UNDECIDED
weightedContrib  UNDECIDED MAKE    = UNDECIDED
weightedContrib  UNDECIDED HELPS   = UNDECIDED
weightedContrib  UNDECIDED SOMEPOS = UNDECIDED
weightedContrib  UNDECIDED ZERO    = UNDECIDED
weightedContrib  UNDECIDED SOMENEG = UNDECIDED
weightedContrib  UNDECIDED HURT    = UNDECIDED
weightedContrib  UNDECIDED BREAK   = UNDECIDED
weightedContrib  NONE      MAKE    = NONE
weightedContrib  NONE      HELPS   = NONE
weightedContrib  NONE      SOMEPOS = NONE
weightedContrib  NONE      ZERO    = NONE
weightedContrib  NONE      SOMENEG = NONE
weightedContrib  NONE      HURT    = NONE
weightedContrib  NONE      BREAK   = NONE
weightedContrib  _         _       = NONE


||| Implementation of the `CompareSatisfiedAndDenied`  resolution
cmpSatAndDen : ContribCount -> SValue
cmpSatAndDen (MkCCount ns _ _ nd _) =
  if ns > 0 && nd > 0
    then CONFLICT
    else if ns > 0 && nd == 0
      then SATISFIED
      else if nd > 0 && ns == 0
        then DENIED
        else NONE

||| Implementation of the `CompareWSandWD` function
cmpWSandWD : ContribCount -> SValue
cmpWSandWD (MkCCount _ nws nwd _ _) =
  if nws > nwd
    then WEAKSATIS
    else if nwd > nws
      then WEAKDEN
      else NONE

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
combineContribs _         _         = NONE
