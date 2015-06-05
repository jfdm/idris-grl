||| A veersion of the GRL with added semantics.
module GRL.Lang.Default

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder

data ValidImpacts : GRLElementTy -> GRLElementTy -> Type where
  GIS : ValidImpacts GOALTy SOFTTy
  SIG : ValidImpacts SOFTTy GOALTy
  TIG : ValidImpacts TASKTy GOALTy
  TIS : ValidImpacts TASKTy SOFTTy
  RIG : ValidImpacts RESOURCETy GOALTy
  RIS : ValidImpacts RESOURCETy GOALTy

data ValidDecomp : GRLElementTy -> GRLElementTy -> Type where
  GHS : ValidDecomp GOALTy SOFTTy
  THT : ValidDecomp TASKTy TASKTy

data GLangTy = E GRLElementTy | L | S

data GLang : GLangTy -> GrlIRTy -> Type where
  MkGoal : String -> Maybe Satisfaction -> GLang (E GOALTy) ELEM
  MkSoft : String -> Maybe Satisfaction -> GLang (E SOFTTy) ELEM
  MkTask : String -> Maybe Satisfaction -> GLang (E TASKTy) ELEM
  MkRes  : String -> Maybe Satisfaction -> GLang (E RESOURCETy) ELEM

  MkImpact : ContributionTy
          -> GLang (E xty) ELEM
          -> GLang (E yty) ELEM
          -> {auto prf : ValidImpacts xty yty}
          -> GLang L INTENT

  MkAnd : GLang (E xty) ELEM
       -> GLang (E yty) ELEM
       -> {auto prf : ValidDecomp xty yty}
       -> GLang S STRUCT

syntax [a] "~" [c] "~>" [b] = MkImpact c a b
syntax [a] "&=" [b]         = MkAnd a b

GOAL : Type
GOAL = GLang (E GOALTy) ELEM

SOFT : Type
SOFT = GLang (E SOFTTy) ELEM

TASK : Type
TASK = GLang (E TASKTy) ELEM

RES : Type
RES = GLang (E RESOURCETy) ELEM

IMPACT : Type
IMPACT = GLang L INTENT

AND : Type
AND = GLang S STRUCT

instance GRL (\x => GLang ty x) where
    mkGoal (MkGoal s e) = Element GOALTy s e
    mkGoal (MkSoft s e) = Element SOFTTy s e
    mkGoal (MkTask s e) = Element TASKTy s e
    mkGoal (MkRes  s e) = Element RESOURCETy s e

    mkIntent (MkImpact c a b) = IntentLink CONTRIBUTION c (mkGoal a) (mkGoal b)

    mkStruct (MkAnd a b) = StructureLink ANDTy (mkGoal a) [(mkGoal b)]

-- --------------------------------------------------------------------- [ EOF ]
