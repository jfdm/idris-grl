-- -------------------------------------------------------------- [ ReSkin.idr ]
-- Module    : ReSkin.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Example DSML through reSkinning the GRL.
module Test.DSML.Paper.ReSkin

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder
import public GRL.Pretty

%access public

-- ---------------------------------------------------------------- [ DSML Def ]
data ETy = PaperTy | SecTy | AuthTy | RevTy | BibTy | AbsTy

data PTy = ElemTy ETy | SLinkTy | ALinkTy

data ValidAction : ETy -> ETy -> Type where
  AS : ValidAction AuthTy SecTy
  RS : ValidAction RevTy  SecTy
  AB : ValidAction AuthTy BibTy
  RB : ValidAction RevTy  BibTy
  AA : ValidAction AuthTy AbsTy
  RA : ValidAction RevTy  AbsTy

data ValidPElem : ETy -> Type where
  SP : ValidPElem SecTy
  BP : ValidPElem BibTy
  AP : ValidPElem AbsTy

data PML : PTy -> GTy -> Type where
  MkPaper : String -> PML (ElemTy PaperTy) ELEM
  MkSect  : String -> PML (ElemTy SecTy)   ELEM
  MkBib   : PML (ElemTy BibTy) ELEM
  MkAbs   : PML (ElemTy AbsTy) ELEM
  MkAuth  : String -> SValue -> PML (ElemTy AuthTy)  ELEM
  MkRev   : String -> SValue -> PML (ElemTy RevTy)   ELEM

  AddElem : PML (ElemTy PaperTy) ELEM
         -> PML (ElemTy x) ELEM
         -> {auto prf : ValidPElem x}
         -> PML SLinkTy STRUCT

  AddAction : PML (ElemTy x) ELEM
           -> PML (ElemTy y) ELEM
           -> {auto prf : ValidAction x y}
           -> PML ALinkTy INTENT

instance GRL (\x => PML ty x) where
  mkElem (MkPaper t) = Elem GOALty t UNKNOWN
  mkElem (MkSect  t) = Elem GOALty t UNKNOWN
  mkElem (MkBib)     = Elem GOALty "Bibliography" UNKNOWN
  mkElem (MkAbs)     = Elem GOALty "Abstract" UNKNOWN

  mkElem (MkAuth t s) = Elem TASKty ("Authoring " ++ t) s
  mkElem (MkRev  t s) = Elem TASKty ("Reviewing " ++ t) s

  mkIntent (AddAction x y) = ILink IMPACTSty MAKES (mkElem x) (mkElem y)

  mkStruct (AddElem x y) = SLink ANDty (mkElem x) [(mkElem y)]

-- ---------------------------------------------------------------- [ MkPretty ]

syntax [a] "==>" [b] = AddAction a b
syntax [a] "&=" [b]  = AddElem a b

PAPER : Type
PAPER = PML (ElemTy PaperTy) ELEM

SECT : Type
SECT = PML (ElemTy SecTy) ELEM

BIB : Type
BIB = PML (ElemTy BibTy) ELEM

ABSTRACT : Type
ABSTRACT = PML (ElemTy AbsTy) ELEM

WRITING : Type
WRITING = PML (ElemTy AuthTy) ELEM

REVIEW : Type
REVIEW = PML (ElemTy RevTy) ELEM

-- ---------------------------------------------------------------- [ Elements ]
paper : PAPER
paper = MkPaper "My First Paper"

abst : ABSTRACT
abst = MkAbs

bib : BIB
bib = MkBib

intro : SECT
intro = MkSect "Introduction"

meth : SECT
meth = MkSect "Methodology"

res : SECT
res = MkSect "Results"

disc : SECT
disc = MkSect "Discussion"

wabs : WRITING
wabs = MkAuth "Abstract" SATISFIED

rabs : REVIEW
rabs = MkRev "Abstract" WEAKSATIS

wbib : WRITING
wbib = MkAuth "Bib" WEAKSATIS

rbib : REVIEW
rbib = MkRev "Bib" WEAKSATIS

wIntro : WRITING
wIntro = MkAuth "Intro" DENIED

rIntro : REVIEW
rIntro = MkRev "Intro" DENIED

wMeth : WRITING
wMeth = MkAuth "Meth" DENIED

rMeth : REVIEW
rMeth = MkRev "Meth" DENIED

wRes : WRITING
wRes = MkAuth "Res" DENIED

rRes : REVIEW
rRes = MkRev "Res" DENIED

wDis : WRITING
wDis = MkAuth "Dis" DENIED

rDis : REVIEW
rDis = MkRev "Dis" DENIED

-- ------------------------------------------------------------------- [ Model ]
paperPlan : GModel
paperPlan = emptyModel
  \= paper
  \= abst  \= wabs   \= rabs
  \= bib   \= wbib   \= rbib
  \= intro \= wIntro \= rIntro
  \= meth  \= wMeth  \= rMeth
  \= res   \= wRes   \= rRes
  \= disc  \= wDis   \= rDis
  \= (paper &= abst)
  \= (paper &= bib)
  \= (paper &= intro)
  \= (paper &= meth)
  \= (paper &= res)
  \= (paper &= disc)
  \= (wabs  ==> abst)
  \= (wbib  ==> bib)
  \= (wIntro ==> intro)
  \= (wMeth ==> meth)
  \= (wRes  ==> res)
  \= (wDis  ==> disc)
  \= (rabs  ==> abst)
  \= (rbib  ==> bib)
  \= (rIntro ==> intro)
  \= (rMeth ==> meth)
  \= (rRes  ==> res)
  \= (rDis  ==> disc)

-- -------------------------------------------------------------------- [ Test ]

runTest : IO ()
runTest = do
    putStrLn $ prettyModel paperPlan
-- --------------------------------------------------------------------- [ EOF ]
