module Test.DSML.Abstract

import GRL.Lang.GLang

data CTy = STy | ATy | BTy

data Comp : (GLang ELEM) -> CTy -> Type where
  Sect : (t:String) -> Comp (MkGoal t Nothing) STy
  Abst : Comp (MkGoal "Abstract" Nothing) ATy
  Bibl : Comp (MkGoal "Biblio" Nothing) BTy


buildStruct : String -> List (GLang ELEM) -> GModel
buildStruct t es = m \= pelem \= (pelem &= es)
  where
    pelem : GLang ELEM
    pelem = MkGoal t Nothing

    m : GModel
    m = insertMany es emptyModel


data Paper : (GModel) -> Type where
  MkPaper : (t : String)
          -> Comp a ATy
          -> Comp b BTy
          -> DList (GLang ELEM) (\x => Comp x STy) ss
          -> Paper (buildStruct t (a :: b :: ss))


addAct : String -> Comp a ty -> SValue -> (GLang ELEM, GLang INTENT)
addAct d _ s {a} = (rtask, (rtask ==> a | MAKES))
  where
    rtask : GLang ELEM
    rtask = MkTask (d ++ getElemTitle a) (Just s)

data TODO : (GLang ELEM, GLang INTENT) -> Type where
  Review : (c : Comp a ty) -> (s : SValue) -> TODO (addAct "Review " c s)
  Write  : (c : Comp a ty) -> (s : SValue) -> TODO (addAct "Writing " c s)

data TList : List (GLang ELEM) -> List (GLang INTENT) -> Type where
  Nil  : TList Nil Nil
  (::) : TODO (x,y) -> TList xs ys -> TList (x::xs) (y::ys)

data PaperToDos : GModel -> Type where
  MkTODO : Paper m
        -> TList es is
        -> PaperToDos (insertMany is $ insertMany es m)


-- --------------------------------------------------------------------- [ EOF ]
