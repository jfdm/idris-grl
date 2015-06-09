module Test.GLang

import GRL.Lang.GLangPlus
import GRL.Eval

highPerf : GOAL
highPerf = MkGoal "High Performance" Nothing

lowCost : SOFT
lowCost = MkSoft "Low Cost" Nothing

foobar : SOFT
foobar = MkSoft "AAA" Nothing

bar : TASK
bar = MkTask "asasas" Nothing

amyotModel : GModel
amyotModel = emptyModel
    \= highPerf
    \= lowCost
    \= foobar
    \= bar
    \= (bar ~~> lowCost | MAKES)
    \= (highPerf &= lowCost)


runTest : IO ()
runTest = do
    printLn "AA"
    putStrLn $ prettyModel amyotModel
