-- -------------------------------------------------------- [ GLang.idr<Paper> ]
-- Module    : GLang.idr<Paper>
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Example paper modelling using the GRL.
module GRL.Test.DSML.Paper.GLang

import GRL.Lang.GLang

%access public

-- ---------------------------------------------------------------- [ Elements ]
paper : GOAL
paper = mkGoal "My First Paper"

abst : GOAL
abst = mkGoal "Abstract"

bib : GOAL
bib = mkGoal "Bibliography"

intro : GOAL
intro = mkGoal "Intro"

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

-- --------------------------------------------------------------- [ Model Def ]

paperPlan : GModel
paperPlan = emptyModel
  \= paper
  \= abst   \= wabs   \= rabs
  \= bib    \= wbib   \= rbib
  \= GLang.intro  \= wIntro \= rIntro
  \= meth   \= wMeth  \= rMeth
  \= res    \= wRes   \= rRes
  \= disc   \= wDis   \= rDis
  \= (paper &= [bib,abst,intro,meth,res,disc])
  \= (wabs   ==> abst  | MAKES)
  \= (wbib   ==> bib   | MAKES)
  \= (wIntro ==> intro | MAKES)
  \= (wMeth  ==> meth  | MAKES)
  \= (wRes   ==> res   | MAKES)
  \= (wDis   ==> disc  | MAKES)
  \= (rabs   ==> abst  | MAKES)
  \= (rbib   ==> bib   | MAKES)
  \= (rIntro ==> intro | MAKES)
  \= (rMeth  ==> meth  | MAKES)
  \= (rRes   ==> res   | MAKES)
  \= (rDis   ==> disc  | MAKES)

-- -------------------------------------------------------------------- [ Test ]
runTest : IO ()
runTest = do
    putStrLn $ prettyModel paperPlan
-- --------------------------------------------------------------------- [ EOF ]
