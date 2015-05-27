||| Definition of the types for the DSL Expressions.
module GRL.Types.Expr

-- ------------------------------------------------------------------- [ Types ]

data GRLElementTy = GOAL | SOFT | TASK | RESOURCE
data GRLIntentTy  = CONTRIBUTION | CORRELATION
data GRLStructTy  = AND | XOR | IOR

data GRLExprTy = ELEM
               | INTENT
               | STRUCT

-- -------------------------------------------------------------------- [ Show ]

instance Show GRLElementTy where
  show GOAL     = "GOAL"
  show SOFT     = "SOFT"
  show TASK     = "TASK"
  show RESOURCE = "RESOURCE"

instance Show GRLIntentTy where
  show CONTRIBUTION = "CONTRIBUTION"
  show CORRELATION  = "CORRELATION"

instance Show GRLStructTy where
  show AND  = "ANDTy"
  show XOR  = "XORTy"
  show IOR  = "IORTy"

instance Show GRLExprTy where
  show ELEM   = "ELEM"
  show INTENT = "INTENT"
  show STRUCT = "STRUCT"

-- ---------------------------------------------------------------------- [ Eq ]

instance Eq GRLElementTy where
  (==) GOAL     GOAL     = True
  (==) SOFT     SOFT     = True
  (==) TASK     TASK     = True
  (==) RESOURCE RESOURCE = True
  (==) _        _        = False

instance Eq GRLIntentTy where
  (==) CONTRIBUTION CONTRIBUTION = True
  (==) CORRELATION  CORRELATION  = True
  (==) _            _            = False

instance Eq GRLStructTy where
  (==) AND AND = True
  (==) XOR XOR = True
  (==) IOR IOR = True
  (==) _   _   = False

instance Eq GRLExprTy where
  (==) ELEM   ELEM   = True
  (==) INTENT INTENT = True
  (==) STRUCT STRUCT = True
  (==) _      _      = False

-- --------------------------------------------------------------------- [ EOF ]
