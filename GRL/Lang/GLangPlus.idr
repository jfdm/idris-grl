||| A veersion of the GRL with added semantics.
module GRL.Lang.GLangPlus

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder
import public GRL.Pretty

%access public

data ValidImpacts : GElemTy -> GElemTy -> Type where
  GIS : ValidImpacts GOALty SOFTty
  SIG : ValidImpacts SOFTty GOALty
  TIG : ValidImpacts TASKty GOALty
  TIS : ValidImpacts TASKty SOFTty
  RIG : ValidImpacts RESty GOALty
  RIS : ValidImpacts RESty GOALty

data ValidDecomp : GElemTy -> GElemTy -> Type where
  GHS : ValidDecomp GOALty SOFTty
  THT : ValidDecomp TASKty TASKty

data GLangPTy = E GElemTy | L | S

data GLang : GLangPTy -> GTy -> Type where
  MkGoal : String -> Maybe SValue -> GLang (E GOALty) ELEM
  MkSoft : String -> Maybe SValue -> GLang (E SOFTty) ELEM
  MkTask : String -> Maybe SValue -> GLang (E TASKty) ELEM
  MkRes  : String -> Maybe SValue -> GLang (E RESty)  ELEM

  MkImpact : CValue
          -> GLang (E xty) ELEM
          -> GLang (E yty) ELEM
          -> {auto prf : ValidImpacts xty yty}
          -> GLang L INTENT

  MkAnd : GLang (E xty) ELEM
       -> GLang (E yty) ELEM
       -> {auto prf : ValidDecomp xty yty}
       -> GLang S STRUCT

syntax [a] "~~>" [b] "|" [c] = MkImpact c a b
syntax [a] "&=" [b]          = MkAnd a b

GOAL : Type
GOAL = GLang (E GOALty) ELEM

SOFT : Type
SOFT = GLang (E SOFTty) ELEM

TASK : Type
TASK = GLang (E TASKty) ELEM

RES : Type
RES = GLang (E RESty) ELEM

IMPACT : Type
IMPACT = GLang L INTENT

AND : Type
AND = GLang S STRUCT

instance GRL (\x => GLang ty x) where
    mkGoal (MkGoal s e) = Elem GOALty s e
    mkGoal (MkSoft s e) = Elem SOFTty s e
    mkGoal (MkTask s e) = Elem TASKty s e
    mkGoal (MkRes  s e) = Elem RESty  s e

    mkIntent (MkImpact c a b) = ILink IMPACTSty c (mkGoal a) (mkGoal b)

    mkStruct (MkAnd a b) = SLink ANDty (mkGoal a) [(mkGoal b)]

-- --------------------------------------------------------------------- [ EOF ]
