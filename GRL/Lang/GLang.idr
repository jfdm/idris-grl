||| The original unabulterated version of the GRL.
module GRL.Lang.GLang

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder
import public GRL.Pretty

%access public

||| The original unadulterated version of the GRL.
data GLang : GTy -> Type where
    MkGoal : String -> Maybe SValue -> GLang ELEM
    MkSoft : String -> Maybe SValue -> GLang ELEM
    MkTask : String -> Maybe SValue -> GLang ELEM
    MkRes  : String -> Maybe SValue -> GLang ELEM

    MkImpacts : CValue -> GLang ELEM -> GLang ELEM -> GLang INTENT
    MkEffects : CValue -> GLang ELEM -> GLang ELEM -> GLang INTENT

    MkAnd : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT
    MkXor : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT
    MkIor : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT

getElemTitle : GLang ELEM -> String
getElemTitle (MkGoal t _) = t
getElemTitle (MkSoft t _) = t
getElemTitle (MkTask t _) = t
getElemTitle (MkRes  t _) = t


GOAL : Type
GOAL = GLang ELEM

SOFT : Type
SOFT = GLang ELEM

TASK : Type
TASK = GLang ELEM

RES : Type
RES = GLang ELEM


syntax [a] "==>" [b] "|" [c] = MkImpacts c a b
syntax [a] "~~>" [b] "|" [c] = MkEffects c a b
syntax [a] "&=" [b] = MkAnd a b
syntax [a] "X=" [b] = MkXor a b
syntax [a] "|=" [b] = MkIor a b


instance GRL GLang where
    mkGoal (MkGoal s e) = Elem GOALty s e
    mkGoal (MkSoft s e) = Elem SOFTty s e
    mkGoal (MkTask s e) = Elem TASKty s e
    mkGoal (MkRes  s e) = Elem RESty  s e

    mkIntent (MkImpacts c a b) = ILink IMPACTSty c (mkGoal a) (mkGoal b)
    mkIntent (MkEffects c a b) = ILink AFFECTSty c (mkGoal a) (mkGoal b)

    mkStruct (MkAnd a bs) = SLink ANDty (mkGoal a) (map (mkGoal) bs)
    mkStruct (MkXor a bs) = SLink XORty (mkGoal a) (map (mkGoal) bs)
    mkStruct (MkIor a bs) = SLink IORty (mkGoal a) (map (mkGoal) bs)

-- --------------------------------------------------------------------- [ EOF ]
