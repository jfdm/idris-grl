-- ---------------------------------------------------------------- [ TODO.idr ]
-- Module    : TODO.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Test.DSML.TODO

import Data.Sigma.DList
import GRL.Lang.GLang

-- ------------------------------------------------------------------- [ Types ]

data Ty = TyITEM | TyTASK

-- ------------------------------------------------------------- [ Interpreter ]

data IRes : Ty -> Type where
  IResItem : GLang ELEM -> IRes TyITEM
  IResTask : GLang ELEM -> GLang INTENT -> IRes TyTASK

interpItem : String -> Maybe SValue -> IRes TyITEM
interpItem title sval = IResItem $ MkGoal title sval

interpTask : String -> SValue -> IRes TyITEM -> IRes TyTASK
interpTask t s (IResItem to) = IResTask elem link
  where
    elem : GLang ELEM
    elem = MkTask t (Just s)

    link : GLang INTENT
    link = (elem ==> to | MAKES)

buildModel : String
          -> List (IRes TyITEM)
          -> List (IRes TyTASK) -> GModel
buildModel n is ts = insertMany tis $ insertMany tes m
  where
    root : GLang ELEM
    root = MkGoal n Nothing

    es : List (GLang ELEM)
    es = map (\(IResItem x) => x) is

    toRoot : GLang STRUCT
    toRoot = (root &= es)

    m : GModel
    m = insert toRoot $ insertMany (root::es) emptyModel

    ties : List (GLang ELEM, GLang INTENT)
    ties = map (\(IResTask e i) => (e,i)) ts

    tis : List (GLang ELEM)
    tis = map fst ties

    tes : List (GLang INTENT)
    tes = map snd ties

-- --------------------------------------------------------- [ Data Structures ]

data TODOItem : (ty : Ty) -> IRes ty -> Type where
  Done : (title : String) -> (desc : Maybe String)
      -> TODOItem TyITEM (interpItem title (Just SATISFIED))

  TODO : (title : String) -> (desc : Maybe String)
      -> TODOItem TyITEM (interpItem title Nothing)

  Action : (title : String) -> (desc : Maybe String)
        -> (value : SValue) -> (todo : TODOItem TyITEM e)
        -> TODOItem TyTASK (interpTask title value e)

data TODOList : GModel -> Type where
  MyList : (name : String)
        -> DList (IRes TyITEM) (\res => TODOItem TyITEM res) is
        -> DList (IRes TyTASK) (\res => TODOItem TyTASK res) ts
        -> TODOList (buildModel name is ts)

-- --------------------------------------------------------------------- [ EOF ]
