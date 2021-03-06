-- --------------------------------------------------------------- [ PTODO.idr ]
-- Module    : PTODO.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Test.DSML.PTODO

import Data.DList
import GRL.Lang.GLang

-- -------------------------------------------------------------- [ Meta Types ]

data Ty = PAPERty | ITEMty | COMPty

data CTy = STy | ATy | BTy

-- ------------------------------------------------------------- [ Interpreter ]

data InterpRes : Ty -> Type where
  ResComp  : GLang ELEM                 -> InterpRes COMPty
  ResPaper : GModel                     -> InterpRes PAPERty
  ResITEM  : GLang ELEM -> GLang INTENT -> InterpRes ITEMty

interpComp : String -> InterpRes COMPty
interpComp t = ResComp $ mkGoal t

interpPaper : String
           -> InterpRes COMPty
           -> InterpRes COMPty
           -> List (InterpRes COMPty)
           -> InterpRes PAPERty
interpPaper s (ResComp a) (ResComp b) es =
    ResPaper $ insert (pelem &= es') m
  where
    pelem : GLang ELEM
    pelem = mkGoal s

    es' : List (GLang ELEM)
    es' = map (\(ResComp e) => e) es

    m : GModel
    m = insertMany (pelem::a::b::es') emptyModel

interpTODO : String
          -> SValue
          -> InterpRes COMPty
          -> InterpRes ITEMty
interpTODO d s (ResComp a) = ResITEM rtask (rtask ==> a | MAKES)
  where
    rtask : GLang ELEM
    rtask = mkSatTask (d ++ getElemTitle a) s

interpTODOS : InterpRes PAPERty
           -> List (InterpRes ITEMty)
           -> GModel
interpTODOS (ResPaper m) es' = insertMany is $ insertMany es m
  where
    is : List (GLang INTENT)
    is = map (\(ResITEM _ i) => i) es'

    es : List (GLang ELEM)
    es = map (\(ResITEM e _) => e) es'

-- ------------------------------------------------------------- [ Definitions ]

data Comp : InterpRes COMPty -> CTy -> Type where
  Sect : (t:String) -> Comp (interpComp t         ) STy
  Abst :               Comp (interpComp "Abstract") ATy
  Bibl :               Comp (interpComp "Biblio"  ) BTy

data Paper : InterpRes PAPERty -> Type where
  MkPaper : (t : String)
         -> Comp a ATy
         -> Comp b BTy
         -> DList (InterpRes COMPty) (\x => Comp x STy) ss
         -> Paper (interpPaper t a b ss)

data TODO : InterpRes ITEMty -> Type where
  Review : (c : Comp a ty)
        -> (s : SValue)
        -> TODO (interpTODO "Review " s a)

  Write  : (c : Comp a ty)
        -> (s : SValue)
        -> TODO (interpTODO "Writing "s a)

data TODOList : GModel -> Type where
  MyList : String
        -> Paper m
        -> DList (InterpRes ITEMty) TODO ts
        -> TODOList (interpTODOS m ts)

-- --------------------------------------------------------------------- [ EOF ]
