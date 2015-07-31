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
abstract
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

-- ------------------------------------------------------------ [ Constructors ]

mkGoal : String -> GLang ELEM
mkGoal t = MkGoal t Nothing

mkSoft : String -> GLang ELEM
mkSoft t = MkSoft t Nothing

mkTask : String -> GLang ELEM
mkTask t = MkTask t Nothing

mkRes : String -> GLang ELEM
mkRes t = MkRes t Nothing


mkSatGoal : String -> Maybe SValue -> GLang ELEM
mkSatGoal = MkGoal

mkSatSoft : String -> Maybe SValue -> GLang ELEM
mkSatSoft = MkSoft

mkSatTask : String -> Maybe SValue -> GLang ELEM
mkSatTask = MkTask

mkSatRes : String -> Maybe SValue -> GLang ELEM
mkSatRes = MkRes


mkImpacts : CValue -> GLang ELEM -> GLang ELEM -> GLang INTENT
mkImpacts = MkImpacts

mkEffects : CValue -> GLang ELEM -> GLang ELEM -> GLang INTENT
mkEffects = MkEffects

mkAnd : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT
mkAnd = MkAnd

mkIor : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT
mkIor = MkIor

mkXor : GLang ELEM -> List (GLang ELEM) -> GLang STRUCT
mkXor = MkXor

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
showElem (MkGoal t s) = with List unwords ["[Goal", t, show s, "]"]
showElem (MkSoft t s) = with List unwords ["[Soft", t, show s, "]"]
showElem (MkTask t s) = with List unwords ["[Task", t, show s, "]"]
showElem (MkRes  t s) = with List unwords ["[Res" , t, show s, "]"]

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
eqGLangE (MkGoal x t) (MkGoal y u) = x == y && t == u
eqGLangE (MkSoft x t) (MkSoft y u) = x == y && t == u
eqGLangE (MkTask x t) (MkTask y u) = x == y && t == u
eqGLangE (MkRes  x t) (MkRes  y u) = x == y && t == u
eqGLangE _            _            = False

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

syntax [a] "==>" [b] "|" [c] = mkImpacts c a b
syntax [a] "~~>" [b] "|" [c] = mkEffects c a b
syntax [a] "&=" [b] = mkAnd a b
syntax [a] "X=" [b] = mkXor a b
syntax [a] "|=" [b] = mkIor a b

-- --------------------------------------------------------------------- [ GRL ]

instance GRL GLang where
    mkElem (MkGoal s v) = Elem GOALty s v
    mkElem (MkSoft s v) = Elem SOFTty s v
    mkElem (MkTask s v) = Elem TASKty s v
    mkElem (MkRes  s v) = Elem RESty  s v

    mkIntent (MkImpacts c a b) = ILink IMPACTSty c (mkElem a) (mkElem b)
    mkIntent (MkEffects c a b) = ILink AFFECTSty c (mkElem a) (mkElem b)

    mkStruct (MkAnd a bs) = SLink ANDty (mkElem a) (map mkElem bs)
    mkStruct (MkXor a bs) = SLink XORty (mkElem a) (map mkElem bs)
    mkStruct (MkIor a bs) = SLink IORty (mkElem a) (map mkElem bs)

-- --------------------------------------------------------------------- [ EOF ]
