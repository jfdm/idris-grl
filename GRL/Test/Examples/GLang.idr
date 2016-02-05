-- ------------------------------------------------------------ [ PaperGRL.idr ]
-- Module    : PaperGRL.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Test.Examples.GLang

import GRL.Lang.GLang

paper : GOAL
paper = mkGoal "My First Paper"

abst : GOAL
abst = mkGoal "Abstract"

bib : GOAL
bib = mkGoal "Bibliography"

intr : GOAL
intr = mkGoal "Intro"

meth : GOAL
meth = mkGoal "Methodology"

res : GOAL
res = mkGoal "Results"

disc : GOAL
disc = mkGoal "Discussion"

wabs : TASK
wabs = mkSatTask "Write Abstract" (SATISFIED)

rabs : TASK
rabs = mkSatTask "Review Abstract" (WEAKSATIS)

wbib : TASK
wbib = mkSatTask "Write Bib" (WEAKSATIS)

rbib : TASK
rbib = mkSatTask "Review Bib" (WEAKSATIS)

wIntro : TASK
wIntro = mkSatTask "Write Intro" (DENIED)

rIntro : TASK
rIntro = mkSatTask "Review Intro" (DENIED)

wMeth : TASK
wMeth = mkSatTask "Write Meth" (DENIED)

rMeth : TASK
rMeth = mkSatTask "Review Meth" (DENIED)

wRes : TASK
wRes = mkSatTask "Write Results" (DENIED)

rRes : TASK
rRes = mkSatTask "Review Results" (DENIED)

wDis : TASK
wDis = mkSatTask "Write Discussion" (DENIED)

rDis : TASK
rDis = mkSatTask "Review Discussion" (DENIED)

paperPlan : GModel
paperPlan = emptyModel
 \= paper
 \= abst   \= wabs   \= rabs   \= bib    \= wbib   \= rbib
 \= intr   \= wIntro \= rIntro \= meth   \= wMeth  \= rMeth
 \= res    \= wRes   \= rRes   \= disc   \= wDis   \= rDis

 \= (paper &= [bib,abst,intr,meth,res,disc])

 \= (wabs   ==> abst  | MAKES)  \= (rabs   ==> abst  | MAKES)
 \= (wbib   ==> bib   | MAKES)  \= (rbib   ==> bib   | MAKES)
 \= (wIntro ==> intr  | MAKES)  \= (rIntro ==> intr  | MAKES)
 \= (wMeth  ==> meth  | MAKES)  \= (rMeth  ==> meth  | MAKES)
 \= (wRes   ==> res   | MAKES)  \= (rRes   ==> res   | MAKES)
 \= (wDis   ==> disc  | MAKES)  \= (rDis   ==> disc  | MAKES)

-- -------------------------------------------------------------------- [ Test ]
export
runTest : IO ()
runTest = do
    putStrLn $ prettyModel paperPlan
-- --------------------------------------------------------------------- [ EOF ]
