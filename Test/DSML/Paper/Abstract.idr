module Test.DSML.Paper.Abstract

import GRL.Lang.GLang
import public Data.Sigma.DList

%access public

data CTy = STy | ATy | BTy

data Comp : GLang ELEM -> CTy -> Type where
  Sect : (t:String) -> Comp (MkGoal t          Nothing) STy
  Abst :               Comp (MkGoal "Abstract" Nothing) ATy
  Bibl :               Comp (MkGoal "Biblio"   Nothing) BTy


modelPaper : String -> GLang ELEM -> GLang ELEM -> List (GLang ELEM) -> GModel
modelPaper t a b es = insert (pelem &= es) m
  where
    pelem : GLang ELEM
    pelem = MkGoal t Nothing

    m : GModel
    m = insert pelem $ insert a $ insert b $ insertMany es emptyModel

data Paper : GModel -> Type where
  MkPaper : (t : String)
         -> Comp a ATy
         -> Comp b BTy
         -> (DList (GLang ELEM) (\x => Comp x STy) ss)
         -> Paper (modelPaper t a b ss)


addAct : String -> GLang ELEM -> SValue -> (GLang ELEM, GLang INTENT)
addAct d s a = (rtask, (rtask ==> a | MAKES))
  where
    rtask : GLang ELEM
    rtask = MkTask (d ++ getElemTitle a) (Just s)

data TODO : (GLang ELEM, GLang INTENT) -> Type where
  Review : (c : Comp a ty) -> (s : SValue) -> TODO (addAct "Review " a s)
  Write  : (c : Comp a ty) -> (s : SValue) -> TODO (addAct "Writing " a s)

data TList : List (GLang ELEM) -> List (GLang INTENT) -> Type where
  Nil  : TList Nil Nil
  (::) : TODO (x,y) -> TList xs ys -> TList (x::xs) (y::ys)

data PaperToDos : GModel -> Type where
  MkTODO : Paper m
        -> TList es is
        -> PaperToDos (insertMany is $ insertMany es m)

-- --------------------------------------------------------------------- [ EOF ]
