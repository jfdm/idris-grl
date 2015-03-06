module GRL.Model.Data

data Weight = HIGH | MEDIUM | LOW | NO

data EvalVal = SATISFIED | WEAKSATIS | WEAKDEN | DENIED | CONFLICT
             | UNKNOWN | NONE | UNDECIDED

data Contrib = MAKES | HELPS | SOMEPOS | ZERO | SOMENEG | HURTS | BREAKS

data ElemTy = MODEL | ELEM | LINK

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
instance Show ElemTy where
  show MODEL  = "MODEL"
  show ELEM   = "ELEM"
  show LINK   = "LINK"

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

readEvalVal : String -> Maybe EvalVal
readEvalVal "satisfied" = Just SATISFIED
readEvalVal "weaksatis" = Just WEAKSATIS
readEvalVal "weakden"   = Just WEAKDEN
readEvalVal "denied"    = Just DENIED
readEvalVal "unknown"   = Just UNKNOWN
readEvalVal _           = Nothing

readContribValue : String -> Maybe Contrib
readContribValue "makes"         = Just MAKES
readContribValue "helps"         = Just HELPS
readContribValue "some-positive" = Just SOMEPOS
readContribValue "zero"          = Just ZERO
readContribValue "some-negative" = Just SOMENEG
readContribValue "hurts"         = Just HURTS
readContribValue "breaks"        = Just BREAKS
readContribValue _               = Nothing



-- --------------------------------------------------------------------- [ EOF ]
