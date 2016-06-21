-- --------------------------------------------------------------- [ CPTML.idr ]
-- Module    : CPTML.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Test.DSML.CPTML

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder
import public GRL.Pretty

%access public export

data Ty = Cyber | Physical

data MTy = AssTy | MechTy Ty | VulnTy Ty | ThreatTy Ty | ILinkTy | SLinkTy

data CPTML : MTy -> GTy -> Type where
  Asset : String -> CPTML AssTy ELEM

  Mech : (ty : Ty) -> String -> CPTML (MechTy ty) ELEM
  Vuln : (ty : Ty) -> String -> CPTML (VulnTy ty) ELEM
  Threat : (ty : Ty) -> String -> CPTML (ThreatTy ty) ELEM

  HasVuln : CPTML (MechTy ty) ELEM
         -> CPTML (VulnTy ty) ELEM
         -> CPTML SLinkTy STRUCT

  Protects : CPTML (MechTy ty) ELEM
          -> CPTML (AssTy) ELEM
          -> CPTML SLinkTy STRUCT

  Manifest : CPTML (ThreatTy xty) ELEM
          -> CPTML (VulnTy   yty) ELEM
          -> CPTML ILinkTy INTENT

GRL (\x => CPTML ty x) where
  mkElem (Asset t)   = Elem GOALty t Nothing
  mkElem (Mech ty t) = Elem GOALty t Nothing
  mkElem (Vuln ty t) = Elem GOALty t Nothing
  mkElem (Threat ty t)  = Elem TASKty t Nothing

  mkStruct (HasVuln x y)  = SLink IORty (mkElem x) [mkElem y]
  mkStruct (Protects x y) = SLink ANDty (mkElem y) [mkElem x]

  mkIntent (Manifest x y) = ILink IMPACTSty BREAK (mkElem x) (mkElem y)





-- --------------------------------------------------------------------- [ EOF ]
