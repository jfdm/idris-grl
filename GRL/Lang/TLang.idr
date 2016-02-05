-- -------------------------------------------------------------- [ ReSkin.idr ]
-- Module    : ReSkin.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| TODO list achieved through reskinning the GRL.
module GRL.Test.DSML.TLang

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder
import public GRL.Pretty

%access public export

-- --------------------------------------------------------- [ DSML Definition ]

data ETy = TaskTy | STaskTy | ActionTy
data TTy = ElemTy ETy | LinkTy | SubLinkTy

data ValidAction : ETy -> ETy -> Type where
  TaskAction    : ValidAction ActionTy TaskTy
  SubTaskAction : ValidAction ActionTy STaskTy

data TLang : TTy -> GTy -> Type where
  MkTask   : String -> TLang (ElemTy TaskTy)   ELEM
  MkSTask  : String -> TLang (ElemTy STaskTy)  ELEM
  MkAction : String -> TLang (ElemTy ActionTy) ELEM

  ActsOn  : CValue
         -> TLang (ElemTy x) ELEM
         -> TLang (ElemTy y) ELEM
         -> {auto prf : ValidAction x y}
         -> TLang LinkTy INTENT

  HasSubTask : TLang (ElemTy TaskTy) ELEM
            -> TLang (ElemTy STaskTy) ELEM
            -> TLang SubLinkTy STRUCT

GRL (\x => TLang ty x) where
  mkElem (MkTask s)   = Elem GOALty s Nothing
  mkElem (MkSTask s)  = Elem GOALty s Nothing
  mkElem (MkAction s) = Elem TASKty s (Just SATISFIED)

  mkIntent (ActsOn c x y) = ILink IMPACTSty c (mkElem x) (mkElem y)

  mkStruct (HasSubTask x y) = SLink ANDty (mkElem x) [(mkElem y)]

-- ------------------------------------------------------------ [ Pretty Stuff ]

syntax [a] "==>" [b] "|" [c] = ActsOn c a b
syntax [a] "&=" [b]          = HasSubTask a b

TASK : Type
TASK = TLang (ElemTy TaskTy) ELEM

SUBTASK : Type
SUBTASK = TLang (ElemTy STaskTy) ELEM

ACTION : Type
ACTION = TLang (ElemTy ActionTy) ELEM

-- --------------------------------------------------------------------- [ EOF ]
