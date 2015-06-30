module Test.DSML.TODO.Abstract

import GRL.Lang.GLang


data Task : (GLang ELEM) -> Type where
  MkTask : (t:String) -> Task (MkGoal t Nothing)
  MkSub  : (t:String) -> Task (MkGoal t Nothing)

data Action : (GLang ELEM) -> Type where
  MkAction : (t:String) -> (s:SValue)
          -> Action (MkTask t (Just s))

data ActsOn : (GLang INTENT) -> Type where
  MkActsOn : (c : CValue) -> Action x -> Task y
          -> ActsOn (MkImpacts c x y)

data HasSubTask : (GLang STRUCT) -> Type where
  LinkTasks : Task x -> Task y
           -> HasSubTask (MkAnd x [y])


data TODO : GModel -> Type where
  MkList : DList (GLang ELEM)   (\x => Task       x) es
        -> DList (GLang ELEM)   (\x => Action     x) as
        -> DList (GLang INTENT) (\x => ActsOn     x) is
        -> DList (GLang STRUCT) (\x => HasSubTask x) ss
        -> TODO (insertMany ss $ insertMany is $ insertMany as $ insertMany es emptyModel)



-- --------------------------------------------------------------------- [ EOF ]
