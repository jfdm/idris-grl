-- --------------------------------------------------------- [ GLang.idr<Test> ]
-- Module    : GLang.idr<Test>
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Test.GLang

import GRL.Lang.GLangPlus
import GRL.Eval

-- ------------------------------------------------------------------- [ Nodes ]
highPerf : GOAL
highPerf = MkGoal "High Performance" Nothing

lowCost : SOFT
lowCost = MkSoft "Low Cost" Nothing

foobar : SOFT
foobar = MkSoft "AAA" Nothing

bar : TASK
bar = MkTask "asasas" Nothing

-- ------------------------------------------------------------------- [ Model ]

amyotModel : GModel
amyotModel = emptyModel
    \= highPerf
    \= lowCost
    \= foobar
    \= bar
    \= (bar ~~> lowCost | MAKES)
    \= (highPerf &= lowCost)

-- -------------------------------------------------------------------- [ Test ]
runTest : IO ()
runTest = do
    printLn "AA"
    putStrLn $ prettyModel amyotModel

-- --------------------------------------------------------------------- [ EOF ]
