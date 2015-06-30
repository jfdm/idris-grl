-- --------------------------------------------------------------- [ GLang.idr ]
-- Module    : GLang.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| The original unadulterated version of the GRL.
module GRL.Lang.GLang

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder
import public GRL.Pretty

%access public
%default total

||| The original unadulterated version of the GRL.
data GLang : GTy -> Type where
    ||| Make a Goal node.
    MkGoal : String -> Maybe SValue -> GLang ELEM
    ||| Make a Soft Goal node.
    MkSoft : String -> Maybe SValue -> GLang ELEM
    ||| Make a Task node.
    MkTask : String -> Maybe SValue -> GLang ELEM
    ||| Make a resource node.
    MkRes  : String -> Maybe SValue -> GLang ELEM

    ||| Declare an impact relation.
    MkImpacts : CValue -> GLang ELEM -> GLang ELEM -> GLang INTENT

    ||| Declare a side-effect relation.
    MkEffects : CValue -> GLang ELEM -> GLang ELEM -> GLang INTENT

    ||| And decomposition relation.
    MkAnd : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT
    ||| XOR decomposition relation.
    MkXor : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT
    ||| IOR decomposition relation.
    MkIor : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT

-- --------------------------------------------------------------- [ Accessors ]

||| Obtain the node's title.
getElemTitle : GLang ELEM -> String
getElemTitle (MkGoal t _) = t
getElemTitle (MkSoft t _) = t
getElemTitle (MkTask t _) = t
getElemTitle (MkRes  t _) = t

||| Quick constructor.
mkG : GElemTy -> String -> Maybe SValue -> GLang ELEM
mkG GOALty = MkGoal
mkG SOFTty = MkSoft
mkG TASKty = MkTask
mkG RESty  = MkRes

-- -------------------------------------------------------------------- [ Sort ]
private
record DeclGroups where
  constructor DGroup
  elems : List (GLang ELEM)
  intes : List (GLang INTENT)
  strus : List (GLang STRUCT)

private
getGroups : DList GTy GLang gs -> DeclGroups
getGroups xs = DList.foldr doGrouping (DGroup Nil Nil Nil) xs
  where
    doGrouping : GLang ty -> DeclGroups -> DeclGroups
    doGrouping {ty=ELEM}   x g = record {elems = x :: (elems g)} g
    doGrouping {ty=INTENT} x g = record {intes = x :: (intes g)} g
    doGrouping {ty=STRUCT} x g = record {strus = x :: (strus g)} g

private
recoverList : DeclGroups -> (ss ** DList GTy GLang ss)
recoverList (DGroup es is ss) =
       (_ ** getProof (fromList es)
          ++ (getProof (fromList is))
          ++ (getProof (fromList ss)))

groupDecls : DList GTy GLang gs -> (gs' ** DList GTy GLang gs')
groupDecls xs = recoverList $ getGroups xs

-- -------------------------------------------------------------------- [ Show ]

private
showElem : GLang ELEM -> String
showElem (MkGoal t sval) = "[Goal " ++ t ++ " " ++ show sval ++ "]"
showElem (MkSoft t sval) = "[Soft " ++ t ++ " " ++ show sval ++ "]"
showElem (MkTask t sval) = "[Task " ++ t ++ " " ++ show sval ++ "]"
showElem (MkRes  t sval) = "[Res "  ++ t ++ " " ++ show sval ++ "]"

private
showIntent : GLang INTENT -> String
showIntent (MkImpacts c a b) = "[Impacts " ++ show c ++ " " ++ showElem a ++ " " ++ showElem b ++ "]"
showIntent (MkEffects c a b) = "[Effects " ++ show c ++ " " ++ showElem a ++ " " ++ showElem b ++ "]"

private
showElems : List (GLang ELEM) -> String
showElems ys = "[" ++ (unwords $ intersperse "," (map showElem ys)) ++ "]"

private
showStruct : GLang STRUCT -> String
showStruct (MkAnd a bs) = "[And " ++ showElem a ++ " " ++ showElems bs ++ "]"
showStruct (MkXor a bs) = "[And " ++ showElem a ++ " " ++ showElems bs ++ "]"
showStruct (MkIor a bs) = "[And " ++ showElem a ++ " " ++ showElems bs ++ "]"

private
showLang : {ty : GTy} -> GLang ty -> String
showLang {ty=ELEM}   x = showElem x
showLang {ty=INTENT} x = showIntent x
showLang {ty=STRUCT} x = showStruct x

instance Show (GLang ty) where
    show x = showLang x

-- ---------------------------------------------------------------------- [ Eq ]

private
eqGLangE : GLang ELEM -> GLang ELEM -> Bool
eqGLangE (MkGoal x s) (MkGoal y t)  = x == y && s == t
eqGLangE (MkSoft x s) (MkSoft y t)  = x == y && s == t
eqGLangE (MkTask x s) (MkTask y t)  = x == y && s == t
eqGLangE (MkRes  x s) (MkRes  y t)  = x == y && s == t
eqGLangE _            _             = False

private
eqGLangI : GLang INTENT -> GLang INTENT -> Bool
eqGLangI (MkImpacts c a b) (MkImpacts d x y) = c == d && eqGLangE a x && eqGLangE b y
eqGLangI (MkEffects c a b) (MkEffects d x y) = c == d && eqGLangE a x && eqGLangE b y
eqGLangI _                 _                 = False

mutual
  private
  eqGLangS : GLang STRUCT -> GLang STRUCT -> Bool
  eqGLangS (MkAnd a as) (MkAnd b bs) = eqGLangE a b && eqGLangList as bs
  eqGLangS (MkXor a as) (MkXor b bs) = eqGLangE a b && eqGLangList as bs
  eqGLangS (MkIor a as) (MkIor b bs) = eqGLangE a b && eqGLangList as bs
  eqGLangS _            _            = False

  private
  eqGLangList : List (GLang ELEM) -> List (GLang ELEM) -> Bool
  eqGLangList Nil     Nil     = True
  eqGLangList (x::xs) (y::ys) =
      if eqGLangE x y
        then eqGLangList xs ys
        else False
  eqGLangList _       _       = False

eqGLang : GLang a -> GLang b -> Bool
eqGLang {a=ELEM}   {b=ELEM}   x y = eqGLangE x y
eqGLang {a=INTENT} {b=INTENT} x y = eqGLangI x y
eqGLang {a=STRUCT} {b=STRUCT} x y = eqGLangS x y
eqGLang _          _              = False

instance Eq (GLang ty) where
  (==) = eqGLang

-- -------------------------------------------------------------- [ Comparable ]

cmpGLang : GLang x -> GLang y -> Ordering
cmpGLang {x} {y} _ _ = compare x y

instance Ord (GLang ty) where
  compare x y = cmpGLang x y

-- ---------------------------------------------------------------- [ Synonyms ]

GOAL : Type
GOAL = GLang ELEM

SOFT : Type
SOFT = GLang ELEM

TASK : Type
TASK = GLang ELEM

RES : Type
RES = GLang ELEM

-- ----------------------------------------------------------- [ Pretty Syntax ]

syntax [a] "==>" [b] "|" [c] = MkImpacts c a b
syntax [a] "~~>" [b] "|" [c] = MkEffects c a b
syntax [a] "&=" [b] = MkAnd a b
syntax [a] "X=" [b] = MkXor a b
syntax [a] "|=" [b] = MkIor a b

-- --------------------------------------------------------------------- [ GRL ]

instance GRL GLang where
    mkGoal (MkGoal s e) = Elem GOALty s e
    mkGoal (MkSoft s e) = Elem SOFTty s e
    mkGoal (MkTask s e) = Elem TASKty s e
    mkGoal (MkRes  s e) = Elem RESty  s e

    mkIntent (MkImpacts c a b) = ILink IMPACTSty c (mkGoal a) (mkGoal b)
    mkIntent (MkEffects c a b) = ILink AFFECTSty c (mkGoal a) (mkGoal b)

    mkStruct (MkAnd a bs) = SLink ANDty (mkGoal a) (map (mkGoal) bs)
    mkStruct (MkXor a bs) = SLink XORty (mkGoal a) (map (mkGoal) bs)
    mkStruct (MkIor a bs) = SLink IORty (mkGoal a) (map (mkGoal) bs)

-- --------------------------------------------------------------------- [ EOF ]
