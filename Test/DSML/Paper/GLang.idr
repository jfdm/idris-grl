-- -------------------------------------------------------- [ GLang.idr<Paper> ]
-- Module    : GLang.idr<Paper>
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Example paper modelling using the GRL.
module Test.DSML.Paper.GLang

import GRL.Lang.GLang

%access public

-- ---------------------------------------------------------------- [ Elements ]
paper : GOAL
paper = MkGoal "My First Paper" Nothing

abst : GOAL
abst = MkGoal "Abstract" Nothing

bib : GOAL
bib = MkGoal "Bibliography" Nothing

intro : GOAL
intro = MkGoal "Intro" Nothing

meth : GOAL
meth = MkGoal "Methodology" Nothing

res : GOAL
res = MkGoal "Results" Nothing

disc : GOAL
disc = MkGoal "Discussion" Nothing

wabs : TASK
wabs = MkTask "Write Abstract" (Just SATISFIED)

rabs : TASK
rabs = MkTask "Review Abstract" (Just WEAKSATIS)

wbib : TASK
wbib = MkTask "Write Bib" (Just WEAKSATIS)

rbib : TASK
rbib = MkTask "Review Bib" (Just WEAKSATIS)

wIntro : TASK
wIntro = MkTask "Write Intro" (Just DENIED)

rIntro : TASK
rIntro = MkTask "Review Intro" (Just DENIED)

wMeth : TASK
wMeth = MkTask "Write Meth" (Just DENIED)

rMeth : TASK
rMeth = MkTask "Review Meth" (Just DENIED)

wRes : TASK
wRes = MkTask "Write Results" (Just DENIED)

rRes : TASK
rRes = MkTask "Review Results" (Just DENIED)

wDis : TASK
wDis = MkTask "Write Discussion" (Just DENIED)

rDis : TASK
rDis = MkTask "Review Discussion" (Just DENIED)

-- --------------------------------------------------------------- [ Model Def ]

paperPlan : GModel
paperPlan = emptyModel
  \= paper
  \= abst   \= wabs   \= rabs
  \= bib    \= wbib   \= rbib
  \= intro  \= wIntro \= rIntro
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
