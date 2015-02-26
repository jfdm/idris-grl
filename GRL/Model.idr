module GRL.Types

import Decidable.Equality

data Weight = HIGH | MEDIUM | LOW | NO

data EvalVal = SATISFIED | WEAKSATIS | WEAKDEN | DENIED | CONFLICT
             | UNKNOWN | NONE | UNDECIDED

data Contrib = MAKES | HELPS | SOMEPOS | ZERO | SOMENEG | HURTS | BREAKS

data ElemTy = MODEL | ELEM | LINK -- | ACTOR

data DecompTy = AND | IOR | XOR

data GModel : ElemTy -> Type where
  -- Model Instance
  GRLSpec : -- List (GModel ACTOR) ->
           List (GModel ELEM)
          -> List (GModel LINK)
          -> GModel MODEL
  -- Elements
  Goal : Maybe String -> EvalVal -> GModel ELEM
  Soft : Maybe String -> EvalVal -> GModel ELEM
  Task : Maybe String -> EvalVal -> GModel ELEM
  Res  : Maybe String -> EvalVal -> GModel ELEM
  -- Actors
  -- Actor : EvalVal
  --       -> String
  --       -> List (GModel ELEM)
  --       -> List (GModel LINK)
  --       -> GModel ACTOR
  -- Intentional
  Impacts : Contrib -> GModel ELEM -> GModel ELEM -> GModel LINK
  Effects : Contrib -> GModel ELEM -> GModel ELEM -> GModel LINK
  -- Structure
  Decomp : DecompTy -> GModel ELEM -> List (GModel ELEM) -> GModel LINK

-- ----------------------------------------------------------- [ Show Instance ]
instance Show ElemTy where
  show MODEL  = "MODEL"
  show ELEM   = "ELEM"
  show LINK   = "LINK"
--  show ACTOR  = "ACTOR"

instance Show DecompTy where
  show AND = "AND"
  show IOR = "IOR"
  show XOR = "XOR"

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
  show ZERO    = "ZERO"
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


instance Eq DecompTy where
  (==) AND AND = True
  (==) IOR IOR = True
  (==) XOR XOR = True
  (==) _   _   = False

instance DecEq DecompTy where
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
  gModelEq (Decomp xty x xs)            (Decomp yty y ys)             = xty == yty && x == y && xs == ys
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
