module GRL.Types

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

instance Show Contrib where
  show MAKES   = "MAKES"
  show HELPS   = "HELPS"
  show SOMEPOS = "SOMEPOS"
  show ZERO    = "ZERO"
  show SOMENEG = "SOMENEG"
  show HURTS   = "HURTS"
  show BREAKS  = "BREAKS"

instance Eq Contrib where
  (==) MAKES   MAKES   = True
  (==) HELPS   HELPS   = True
  (==) SOMEPOS SOMEPOS = True
  (==) ZERO    ZERO    = True
  (==) SOMENEG SOMENEG = True
  (==) HURTS   HURTS   = True
  (==) BREAKS  BREAKS  = True
  (==) _       _       = False

-- --------------------------------------------------------------------- [ EOF ]
