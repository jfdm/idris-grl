-- ------------------------------------------------------------ [ Abstract.idr ]
-- Module    : Abstract.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| TODO List using abstract interpretation
module Test.DSML.TODO.Abstract

import GRL.Lang.GLang

||| Specify Task.
data Task : (GLang ELEM) -> Type where
  MkTask : (t:String) -> Task (MkGoal t Nothing)
  MkSub  : (t:String) -> Task (MkGoal t Nothing)

||| Specify action
data Action : (GLang ELEM) -> Type where
  MkAction : (t:String) -> (s:SValue)
          -> Action (MkTask t (Just s))

||| Specify task relation.
data ActsOn : (GLang INTENT) -> Type where
  MkActsOn : (c : CValue) -> Action x -> Task y
          -> ActsOn (MkImpacts c x y)

||| Specify sub task
data HasSubTask : (GLang STRUCT) -> Type where
  LinkTasks : Task x -> Task y
           -> HasSubTask (MkAnd x [y])

||| The todo list
data TODO : GModel -> Type where
  MkList : DList (GLang ELEM)   (\x => Task       x) es
        -> DList (GLang ELEM)   (\x => Action     x) as
        -> DList (GLang INTENT) (\x => ActsOn     x) is
        -> DList (GLang STRUCT) (\x => HasSubTask x) ss
        -> TODO (insertMany ss $ insertMany is $ insertMany as $ insertMany es emptyModel)

-- --------------------------------------------------------------------- [ EOF ]
