||| Common enumerated types used.
module GRL.Common

import public Decidable.Equality

data Decomposition  = ANDTy | XORTy | IORTy

data Importance = HIGH | MEDIUM | LOW | NO

namespace Qualiative
  data Satisfaction : Type where
    ||| The intentional element or indicator is sufficiently dissatisfied.
    DENIED : Satisfaction
    ||| The intentional element is partially dissatisfied.
    WEAKDEN : Satisfaction
    ||| The intentional element or indicator is partially satisfied.
    WEAKSATIS : Satisfaction
    ||| The intentional element is sufficiently satisfied.
    SATISFIED   : Satisfaction
    ||| There are arguments strongly in favour and strongly against
    ||| the satisfaction of the intentional element.
    CONFLICT : Satisfaction
    ||| The satisfaction level of the intentional element is unknown.
    UNKNOWN : Satisfaction
    ||| The intentional element or indicator is neither satisfied nor dissatisfied.
    NONE : Satisfaction
    UNDECIDED : Satisfaction

namespace Contributions
  data ContributionTy : Type where
    ||| The contribution is positive and sufficient.
    MAKES : ContributionTy
    ||| The contribution is positive but not sufficient.
    HELPS : ContributionTy
    ||| The contribution is positive, but the extent of the contribution is unknown.
    SOMEPOS : ContributionTy
    ||| There is some contribution, but the extent and the degree (positive or negative) of the contribution is unknown.
    UNKNOWN : ContributionTy
    ||| The contribution is negative, but the extent of the contribution is unknown.
    SOMENEG : ContributionTy
    ||| The contribution of the contributing element is negative and sufficient.
    BREAKS : ContributionTy
    ||| The contribution is negative but not sufficient.
    HURTS : ContributionTy


-- ------------------------------------------------------------------- [ Types ]

data GRLElementTy = GOALTy | SOFTTy | TASKTy | RESOURCETy

data GRLIntentTy  = CONTRIBUTION | CORRELATION

data GrlIRTy = ELEM
               | INTENT
               | STRUCT

-- -------------------------------------------------------------------- [ Show ]

instance Show GRLElementTy where
  show GOALTy     = "GOALTy"
  show SOFTTy     = "SOFTTy"
  show TASKTy     = "TASKTy"
  show RESOURCETy = "RESOURCETy"

instance Show GRLIntentTy where
  show CONTRIBUTION = "CONTRIBUTION"
  show CORRELATION  = "CORRELATION"

instance Show GrlIRTy where
  show ELEM   = "ELEM"
  show INTENT = "INTENT"
  show STRUCT = "STRUCT"

-- ---------------------------------------------------------------------- [ Eq ]

instance Eq GRLElementTy where
  (==) GOALTy     GOALTy     = True
  (==) SOFTTy     SOFTTy     = True
  (==) TASKTy     TASKTy     = True
  (==) RESOURCETy RESOURCETy = True
  (==) _        _        = False

instance Eq GRLIntentTy where
  (==) CONTRIBUTION CONTRIBUTION = True
  (==) CORRELATION  CORRELATION  = True
  (==) _            _            = False

instance Eq GrlIRTy where
  (==) ELEM   ELEM   = True
  (==) INTENT INTENT = True
  (==) STRUCT STRUCT = True
  (==) _      _      = False

-- -------------------------------------------------------------------- [ Show ]

instance Show Decomposition where
  show ANDTy  = "ANDTy"
  show XORTy  = "XORTy"
  show IORTy  = "IORTy"

instance Show Satisfaction where
  show SATISFIED = "SATISFIED"
  show WEAKSATIS = "WEAKSATIS"
  show WEAKDEN   = "WEAKDEN"
  show DENIED    = "DENIED"
  show CONFLICT  = "CONFLICT"
  show UNKNOWN   = "UNKNOWN"
  show NONE      = "NONE"
  show UNDECIDED = "UNDECIDED"

instance Show ContributionTy where
  show MAKES   = "MAKES"
  show HELPS   = "HELPS"
  show SOMEPOS = "SOMEPOS"
  show UNKNOWN    = "UNKNOWN"
  show SOMENEG = "SOMENEG"
  show HURTS   = "HURTS"
  show BREAKS  = "BREAKS"

-- ---------------------------------------------------------------------- [ Eq ]
instance Eq Decomposition where
  (==) ANDTy ANDTy = True
  (==) XORTy XORTy = True
  (==) IORTy IORTy = True
  (==) _   _   = False

instance Eq Satisfaction where
  (==) SATISFIED SATISFIED = True
  (==) WEAKSATIS WEAKSATIS = True
  (==) WEAKDEN   WEAKDEN   = True
  (==) DENIED    DENIED    = True
  (==) CONFLICT  CONFLICT  = True
  (==) UNKNOWN   UNKNOWN   = True
  (==) NONE      NONE      = True
  (==) UNDECIDED UNDECIDED = True
  (==) _         _         = False

instance Eq ContributionTy where
  (==) MAKES   MAKES   = True
  (==) HELPS   HELPS   = True
  (==) SOMEPOS SOMEPOS = True
  (==) UNKNOWN    UNKNOWN    = True
  (==) SOMENEG SOMENEG = True
  (==) HURTS   HURTS   = True
  (==) BREAKS  BREAKS  = True
  (==) _       _       = False


-- -------------------------------------------------------------------- [ Read ]
readSatisfaction : String -> Satisfaction
readSatisfaction "satisfied" = SATISFIED
readSatisfaction "weaksatis" = WEAKSATIS
readSatisfaction "weakden"   = WEAKDEN
readSatisfaction "denied"    = DENIED
readSatisfaction "unknown"   = UNKNOWN
readSatisfaction _           = UNKNOWN

readContribValue : String -> ContributionTy
readContribValue "makes"         = MAKES
readContribValue "helps"         = HELPS
readContribValue "some-positive" = SOMEPOS
readContribValue "unknown"       = UNKNOWN
readContribValue "some-negative" = SOMENEG
readContribValue "hurts"         = HURTS
readContribValue "breaks"        = BREAKS
readContribValue _               = UNKNOWN


-- ------------------------------------------------------------------- [ DecEq ]
instance DecEq Satisfaction where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void


instance DecEq ContributionTy where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void
-- --------------------------------------------------------------------- [ EOF ]
