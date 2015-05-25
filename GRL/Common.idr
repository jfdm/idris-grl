||| Common data structures for GRL the model and edsl.
module GRL.Common

import public Decidable.Equality

data Weight = HIGH | MEDIUM | LOW | NO

namespace Qualiative
  data EvalVal : Type where

    ||| The intentional element or indicator is sufficiently dissatisfied.
    DENIED : EvalVal

    ||| The intentional element is partially dissatisfied.
    WEAKDEN : EvalVal

    ||| The intentional element or indicator is partially satisfied.
    WEAKSATIS : EvalVal


    ||| The intentional element is sufficiently satisfied.
    SATISFIED   : EvalVal

    ||| There are arguments strongly in favour and strongly against
    ||| the satisfaction of the intentional element.
    CONFLICT : EvalVal

    ||| The satisfaction level of the intentional element is unknown.
    UNKNOWN : EvalVal

    ||| The intentional element or indicator is neither satisfied nor dissatisfied.
    NONE : EvalVal

    UNDECIDED : EvalVal

namespace Contributions
  data Contrib : Type where
    ||| The contribution is positive and sufficient.
    MAKES    : Contrib
    ||| The contribution is positive but not sufficient.
    HELPS    : Contrib
    ||| The contribution is positive, but the extent of the contribution is unknown.
    SOMEPOS  : Contrib
    ||| There is some contribution, but the extent and the degree (positive or negative) of the contribution is unknown.
    UNKNOWN     : Contrib
    ||| The contribution is negative, but the extent of the contribution is unknown.
    SOMENEG  : Contrib
    ||| The contribution of the contributing element is negative and sufficient.
    BREAKS   : Contrib
    ||| The contribution is negative but not sufficient.
    HURTS    : Contrib


data ElemTy = MODEL | ELEM | ILINK | SLINK

data DecompTy = ANDTy | XORTy | IORTy

-- -------------------------------------------------------------------- [ Show ]
instance Show ElemTy where
  show MODEL  = "MODEL"
  show ELEM   = "ELEM"
  show LINK   = "LINK"

instance Show DecompTy where
  show ANDTy  = "ANDTy"
  show XORTy  = "XORTy"
  show IORTy  = "IORTy"

instance Show EvalVal where
  show SATISFIED = "SATISFIED"
  show WEAKSATIS = "WEAKSATIS"
  show WEAKDEN   = "WEAKDEN"
  show DENIED    = "DENIED"
  show CONFLICT  = "CONFLICT"
  show UNKNOWN   = "UNKNOWN"
  show NONE      = "NONE"
  show UNDECIDED = "UNDECIDED"

instance Show Contrib where
  show MAKES   = "MAKES"
  show HELPS   = "HELPS"
  show SOMEPOS = "SOMEPOS"
  show UNKNOWN    = "UNKNOWN"
  show SOMENEG = "SOMENEG"
  show HURTS   = "HURTS"
  show BREAKS  = "BREAKS"

-- ---------------------------------------------------------------------- [ Eq ]
instance Eq EvalVal where
  (==) SATISFIED SATISFIED = True
  (==) WEAKSATIS WEAKSATIS = True
  (==) WEAKDEN   WEAKDEN   = True
  (==) DENIED    DENIED    = True
  (==) CONFLICT  CONFLICT  = True
  (==) UNKNOWN   UNKNOWN   = True
  (==) NONE      NONE      = True
  (==) UNDECIDED UNDECIDED = True
  (==) _         _         = False

instance Eq Contrib where
  (==) MAKES   MAKES   = True
  (==) HELPS   HELPS   = True
  (==) SOMEPOS SOMEPOS = True
  (==) UNKNOWN    UNKNOWN    = True
  (==) SOMENEG SOMENEG = True
  (==) HURTS   HURTS   = True
  (==) BREAKS  BREAKS  = True
  (==) _       _       = False


instance Eq DecompTy where
  (==) ANDTy ANDTy = True
  (==) XORTy XORTy = True
  (==) IORTy IORTy = True
  (==) _     _     = False

-- -------------------------------------------------------------------- [ Read ]
readEvalVal : String -> EvalVal
readEvalVal "satisfied" = SATISFIED
readEvalVal "weaksatis" = WEAKSATIS
readEvalVal "weakden"   = WEAKDEN
readEvalVal "denied"    = DENIED
readEvalVal "unknown"   = UNKNOWN
readEvalVal _           = UNKNOWN

readContribValue : String -> Contrib
readContribValue "makes"         = MAKES
readContribValue "helps"         = HELPS
readContribValue "some-positive" = SOMEPOS
readContribValue "unknown"       = UNKNOWN
readContribValue "some-negative" = SOMENEG
readContribValue "hurts"         = HURTS
readContribValue "breaks"        = BREAKS
readContribValue _               = UNKNOWN


-- ------------------------------------------------------------------- [ DecEq ]
instance DecEq EvalVal where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void


instance DecEq Contrib where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void
-- --------------------------------------------------------------------- [ EOF ]
