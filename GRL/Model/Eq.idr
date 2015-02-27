module GRL.Model.Eq

import public Decidable.Equality
import GRL.Model.Data

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

instance DecEq EvalVal where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void

instance Eq Contrib where
  (==) MAKES   MAKES   = True
  (==) HELPS   HELPS   = True
  (==) SOMEPOS SOMEPOS = True
  (==) ZERO    ZERO    = True
  (==) SOMENEG SOMENEG = True
  (==) HURTS   HURTS   = True
  (==) BREAKS  BREAKS  = True
  (==) _       _       = False

instance DecEq Contrib where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void

-- @TODO Make total.
mutual
  %assert_total
  gModelEq : (GModel x) -> (GModel y) -> Bool
  gModelEq (GRLSpec (x::xes) (x'::xls)) (GRLSpec (y::yes) (y'::yls))  = x == y && xes == yes && x' == y' && xls == yls
  gModelEq (Goal x xe)                  (Goal y ye)                   = x == y && xe == ye
  gModelEq (Soft x xe)                  (Soft y ye)                   = x == y && xe == ye
  gModelEq (Task x xe)                  (Task y ye)                   = x == y && xe == ye
  gModelEq (Res x xe)                   (Res y ye)                    = x == y && xe == ye
  gModelEq (Impacts xc xa xb)           (Impacts yc ya yb)            = xc == yc && xa == ya && xb == yb
  gModelEq (Effects xc xa xb)           (Effects yc ya yb)            = xc == yc && xa == ya && xb == yb
  gModelEq (AND x xs)                   (AND y ys)                    = x == y && xs == ys
  gModelEq (XOR x xs)                   (XOR y ys)                    = x == y && xs == ys
  gModelEq (IOR x xs)                   (IOR y ys)                    = x == y && xs == ys
  gModelEq _                            _                             = False

  instance Eq (GModel ty) where
    (==) = gModelEq

-- ------------------------------------------------------ [ Decidable Equality ]

instance DecEq (GModel ty) where
  decEq x y = if x == y then Yes primEq else No primNotEq
    where
      primEq : x = y
      primEq = believe_me (Refl {x})
      postulate primNotEq : x = y -> Void

-- --------------------------------------------------------------------- [ EOF ]
