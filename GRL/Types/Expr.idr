||| Definition of the types for the DSL Expressions.
module GRL.Types.Expr

-- ------------------------------------------------------------------- [ Types ]

data GRLElementTy = GOALTy | SOFTTy | TASKTy | RESOURCETy
data GRLIntentTy  = CONTRIBUTION | CORRELATION
data GRLStructTy  = ANDTy | XORTy | IORTy

data GRLExprTy = ELEM
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

instance Show GRLStructTy where
  show ANDTy  = "ANDTy"
  show XORTy  = "XORTy"
  show IORTy  = "IORTy"

instance Show GRLExprTy where
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

instance Eq GRLStructTy where
  (==) ANDTy ANDTy = True
  (==) XORTy XORTy = True
  (==) IORTy IORTy = True
  (==) _   _   = False

instance Eq GRLExprTy where
  (==) ELEM   ELEM   = True
  (==) INTENT INTENT = True
  (==) STRUCT STRUCT = True
  (==) _      _      = False

-- --------------------------------------------------------------------- [ EOF ]
