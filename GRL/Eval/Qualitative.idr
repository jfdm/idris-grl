||| Qualitative evaluations for
module GRL.Eval.Qualitative

import public Effects
import public Effect.State
import public Effect.Exception

import GRL.Model

%access public

private
andCompare : EvalVal -> EvalVal -> Ordering
andCompare SATISFIED SATISFIED = EQ
andCompare WEAKSATIS WEAKSATIS = EQ
andCompare WEAKDEN   WEAKDEN   = EQ
andCompare DENIED    DENIED    = EQ
andCompare CONFLICT  CONFLICT  = EQ
andCompare UNKNOWN   UNKNOWN   = EQ
andCompare NONE      NONE      = EQ
andCompare UNDECIDED UNDECIDED = EQ
andCompare DENIED    _         = LT
andCompare _         DENIED    = GT
andCompare CONFLICT  UNDECIDED = EQ
andCompare UNDECIDED CONFLICT  = EQ
andCompare CONFLICT  _         = LT
andCompare _         CONFLICT  = GT
andCompare UNDECIDED _         = LT
andCompare _         UNDECIDED = GT
andCompare WEAKDEN   _         = LT
andCompare _         WEAKDEN   = GT
andCompare NONE      _         = LT
andCompare _         NONE      = GT
andCompare WEAKSATIS _         = LT
andCompare _         WEAKSATIS = GT
andCompare SATISFIED _         = GT
andCompare _         SATISFIED = LT

getDecompAnd : List EvalVal -> EvalVal
getDecompAnd [e]     = e
getDecompAnd (e::es) = doCompare e es
 where
  doCompare : EvalVal -> List EvalVal -> EvalVal
  doCompare e  Nil     = e
  doCompare e' (e::es) = case andCompare e' e of
    LT => doCompare e' es
    GT => doCompare e es
    EQ => doCompare e es

private
orCompare : EvalVal -> EvalVal -> Ordering
orCompare SATISFIED SATISFIED = EQ
orCompare WEAKSATIS WEAKSATIS = EQ
orCompare WEAKDEN   WEAKDEN   = EQ
orCompare DENIED    DENIED    = EQ
orCompare CONFLICT  CONFLICT  = EQ
orCompare UNKNOWN   UNKNOWN   = EQ
orCompare NONE      NONE      = EQ
orCompare UNDECIDED UNDECIDED = EQ
orCompare DENIED    _         = LT
orCompare _         DENIED    = GT
orCompare WEAKDEN   _         = LT
orCompare _         WEAKDEN   = GT
orCompare NONE      _         = LT
orCompare _         NONE      = GT
orCompare WEAKSATIS _         = LT
orCompare _         WEAKSATIS = GT
orCompare CONFLICT  UNDECIDED = EQ
orCompare UNDECIDED CONFLICT  = EQ
orCompare CONFLICT  _         = LT
orCompare _         CONFLICT  = GT
orCompare UNDECIDED _         = LT
orCompare _         UNDECIDED = GT
orCompare SATISFIED _         = GT
orCompare _         SATISFIED = LT

getDecompOR : List EvalVal -> EvalVal
getDecompOR [e]     = e
getDecompOR (e::es) = doCompare e es
 where
  doCompare : EvalVal -> List EvalVal -> EvalVal
  doCompare e  Nil     = e
  doCompare e' (e::es) = case andCompare e' e of
    LT => doCompare e es
    GT => doCompare e' es
    EQ => doCompare e es

record ContribCount where
  constructor MkCCount
  noSatis  : Nat
  noWeakS  : Nat
  noWeakD  : Nat
  noDenied : Nat
  noUndec  : Nat

||| Implementation of `AdjustContributionCounters`
adJustCount : ContribCount -> EvalVal -> ContribCount
adJustCount cnt SATISFIED = record {noSatis = (S (noSatis cnt))} cnt
adJustCount cnt WEAKSATIS = record {noWeakS = (S (noWeakS cnt))} cnt
adJustCount cnt WEAKDEN   = record {noWeakD = (S (noWeakD cnt))} cnt
adJustCount cnt UNDECIDED = record {noUndec = (S (noUndec cnt))} cnt
adJustCount cnt _         = cnt

||| Implementation of `AdjustContributionCounters` for a list of values.
adjustCounts : List EvalVal -> ContribCount
adjustCounts es = foldl adJustCount (MkCCount 0 0 0 0 0) es

||| Implementation of the `WeightedContribution` look up table.
%inline
weightedContribution : EvalVal -> Contrib -> EvalVal
weightedContribution  DENIED    MAKE    = DENIED
weightedContribution  DENIED    HELP    = WEAKDEN
weightedContribution  DENIED    SOMEPOS = WEAKDEN
weightedContribution  DENIED    ZERO    = NONE
weightedContribution  DENIED    SOMENEG = WEAKSATIS
weightedContribution  DENIED    HURT    = WEAKSATIS
weightedContribution  DENIED    BREAK   = SATISFIED
weightedContribution  WEAKDEN   MAKE    = WEAKDEN
weightedContribution  WEAKDEN   HELP    = WEAKDEN
weightedContribution  WEAKDEN   SOMEPOS = WEAKDEN
weightedContribution  WEAKDEN   ZERO    = NONE
weightedContribution  WEAKDEN   SOMENEG = WEAKSATIS
weightedContribution  WEAKDEN   HURT    = WEAKSATIS
weightedContribution  WEAKDEN   BREAK   = WEAKSATIS
weightedContribution  WEAKSATIS MAKE    = WEAKSATIS
weightedContribution  WEAKSATIS HELP    = WEAKSATIS
weightedContribution  WEAKSATIS SOMEPOS = WEAKSATIS
weightedContribution  WEAKSATIS ZERO    = NONE
weightedContribution  WEAKSATIS SOMENEG = WEAKDEN
weightedContribution  WEAKSATIS HURT    = WEAKDEN
weightedContribution  WEAKSATIS BREAK   = WEAKDEN
weightedContribution  SATISFIED MAKE    = SATISFIED
weightedContribution  SATISFIED HELP    = WEAKSATIS
weightedContribution  SATISFIED SOMEPOS = WEAKSATIS
weightedContribution  SATISFIED ZERO    = NONE
weightedContribution  SATISFIED SOMENEG = WEAKDEN
weightedContribution  SATISFIED HURT    = WEAKDEN
weightedContribution  SATISFIED BREAK   = DENIED
weightedContribution  CONFLICT  MAKE    = UNDECIDED
weightedContribution  CONFLICT  HELP    = UNDECIDED
weightedContribution  CONFLICT  SOMEPOS = UNDECIDED
weightedContribution  CONFLICT  ZERO    = UNDECIDED
weightedContribution  CONFLICT  SOMENEG = UNDECIDED
weightedContribution  CONFLICT  HURT    = UNDECIDED
weightedContribution  CONFLICT  BREAK   = UNDECIDED
weightedContribution  UNDECIDED MAKE    = UNDECIDED
weightedContribution  UNDECIDED HELP    = UNDECIDED
weightedContribution  UNDECIDED SOMEPOS = UNDECIDED
weightedContribution  UNDECIDED ZERO    = UNDECIDED
weightedContribution  UNDECIDED SOMENEG = UNDECIDED
weightedContribution  UNDECIDED HURT    = UNDECIDED
weightedContribution  UNDECIDED BREAK   = UNDECIDED
weightedContribution  NONE      MAKE    = NONE
weightedContribution  NONE      HELP    = NONE
weightedContribution  NONE      SOMEPOS = NONE
weightedContribution  NONE      ZERO    = NONE
weightedContribution  NONE      SOMENEG = NONE
weightedContribution  NONE      HURT    = NONE
weightedContribution  NONE      BREAK   = NONE

||| Implementation of the `CompareSatisfiedAndDenied`  resolution
compareSatAndDen : ContribCount -> EvalVal
compareSatAndDen (MkCCount ns _ _ nd _) =
  if ns > 0 && nd > 0
    then CONFLICT
    else if ns > 0 && nd == 0
      then SATISFIED
      else if nd > 0 && ns == 0
        then DENIED
        else NONE

||| Implementation of the `CompareWSandWD` function
compareWSandWD : ContribCount -> EvalVal
compareWSandWD (MkCCount _ nws nwd _ _) =
  if nws > nwd
    then WEAKSATIS
    else if nwd > nws
      then WEAKDEN
      else NONE

||| Implementation of the `CombineContributions` function
%inline
combineContrib : EvalVal -> EvalVal -> EvalVal
combineContrib WEAKDEN   DENIED    = DENIED
combineContrib WEAKDEN   SATISFIED = WEAKSATIS
combineContrib WEAKDEN   CONFLICT  = CONFLICT
combineContrib WEAKDEN   NONE      = WEAKDEN
combineContrib WEAKSATIS DENIED    = WEAKDEN
combineContrib WEAKSATIS SATISFIED = SATISFIED
combineContrib WEAKSATIS CONFLICT  = CONFLICT
combineContrib WEAKSATIS NONE      = WEAKSATIS
combineContrib NONE      DENIED    = DENIED
combineContrib NONE      SATISFIED = SATISFIED
combineContrib NONE      CONFLICT  = CONFLICT
combineContrib NONE      NONE      = NONE
