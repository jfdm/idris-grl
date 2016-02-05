-- --------------------------------------------------------------- [ Model.idr ]
-- Module    : Model.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Example of using PML to model a paper.
module GRL.Test.Examples.PML

import GRL.Lang.PML

-- ------------------------------------------------------------------- [ Paper ]

paper : PAPER
paper = MkPaper "My First Paper"

abst : ABSTRACT
abst = MkAbs

bib : BIB
bib = MkBib

intr : SECT
intr = MkSect "Introduction"

meth : SECT
meth = MkSect "Methodology"

res : SECT
res = MkSect "Results"

disc : SECT
disc = MkSect "Discussion"

-- ------------------------------------------------------------------- [ Tasks ]

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

-- ------------------------------------------------------------- [ Build Model ]

paperPlan : GModel
paperPlan = emptyModel
 \= paper
 \= abst  \= wabs   \= rabs    \= bib   \= wbib   \= rbib
 \= intr  \= wIntro \= rIntro  \= meth  \= wMeth  \= rMeth
 \= res   \= wRes   \= rRes    \= disc  \= wDis   \= rDis

 \= (paper &= abst)  \= (wabs  ==> abst)  \= (rabs  ==> abst)
 \= (paper &= bib)   \= (wbib  ==> bib)   \= (rbib  ==> bib)
 \= (paper &= intr)  \= (wIntro ==> intr) \= (rIntro ==> intr)
 \= (paper &= meth)  \= (wMeth ==> meth)  \= (rMeth ==> meth)
 \= (paper &= res)   \= (wRes  ==> res)   \= (rRes  ==> res)
 \= (paper &= disc)  \= (wDis  ==> disc)  \= (rDis  ==> disc)

 -- -------------------------------------------------------------------- [ Test ]
export
runTest : IO ()
runTest = do
    putStrLn $ prettyModel paperPlan

-- --------------------------------------------------------------------- [ EOF ]
