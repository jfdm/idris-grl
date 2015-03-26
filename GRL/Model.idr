module GRL.Model

import public GRL.Common

data GModel : ElemTy -> Type where
  -- Model Instance
  GRLSpec : List (GModel ELEM) -> List (GModel LINK) -> GModel MODEL
  -- Elements
  Goal : Maybe String -> EvalVal -> GModel ELEM
  Soft : Maybe String -> EvalVal -> GModel ELEM
  Task : Maybe String -> EvalVal -> GModel ELEM
  Res  : Maybe String -> EvalVal -> GModel ELEM
  -- Intentional
  Impacts : Contrib -> GModel ELEM -> GModel ELEM -> GModel LINK
  Effects : Contrib -> GModel ELEM -> GModel ELEM -> GModel LINK
  -- Structure
  AND : GModel ELEM -> List (GModel ELEM) -> GModel LINK
  XOR : GModel ELEM -> List (GModel ELEM) -> GModel LINK
  IOR : GModel ELEM -> List (GModel ELEM) -> GModel LINK

-- ----------------------------------------------------------- [ Show Instance ]

instance Show (GModel ty) where
  show (GRLSpec es ls) = unwords ["[Model ", show es, show ls, "]\n"]
  show (Goal t v)      = unwords ["[Goal ", show t, show v, "]"]
  show (Task t v)      = unwords ["[Task ", show t, show v, "]"]
  show (Soft t v)      = unwords ["[Soft ", show t, show v, "]"]
  show (Res t v)       = unwords ["[Res ", show t, show v, "]"]

  show (Impacts c a b) = unwords ["[Impacts ", show a, show c, show b, "]\n"]
  show (Effects c a b) = unwords ["[Effects ", show a, show c, show b, "]\n"]

  show (AND e es) = unwords ["[", show e, "&&", show es, "]"]
  show (XOR e es) = unwords ["[", show e, "XOR", show es, "]"]
  show (IOR e es) = unwords ["[", show e, "||", show es, "]"]

-- ---------------------------------------------------------------------- [ Eq ]

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
