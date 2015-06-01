module DSL.Lang.AST

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


-- ---------------------------------------------------------- [ ADT Definition ]
data GRLExpr : GRLExprTy -> Type where
  Element : (ty : GRLElementTy)
          -> String
          -> Maybe Satisfaction
          -> GRLExpr ELEM

  IntentLink : (ty : GRLIntentTy)
           -> ContributionTy
           -> GRLExpr ELEM
           -> GRLExpr ELEM
           -> GRLExpr INTENT

  StructureLink : (ty : GRLStructTy)
               -> GRLExpr ELEM
               -> List (GRLExpr ELEM)
               -> GRLExpr STRUCT

partial
eqGRLExpr : GRLExpr a -> GRLExpr b -> Bool
eqGRLExpr (Element xty x sx) (Element yty y sy) =
    xty == yty && x == y && sx == sy
eqGRLExpr (IntentLink xty xc xa xb) (IntentLink yty yc ya yb) =
    xty == yty && xc == yc && eqGRLExpr xa ya && eqGRLExpr xb yb
eqGRLExpr (StructureLink xty xa (xbs)) (StructureLink yty ya (ybs)) =
      xty == yty && eqGRLExpr xa ya && eqGRLExprList xbs ybs
    where
      eqGRLExprList : List (GRLExpr ELEM) -> List (GRLExpr ELEM) -> Bool
      eqGRLExprList Nil Nil = True
      eqGRLExprList Nil ys  = False
      eqGRLExprList (x::xs) (y::ys) = eqGRLExpr x y && assert_smaller (eqGRLExprList xs ys) (eqGRLExprList xs ys)
eqGRLExpr _ _ = False

-- --------------------------------------------------------------------- [ EOF ]
