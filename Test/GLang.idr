module Test.Amyot

import GRL.Lang.GLang
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

ppRes : Show a => List (a) -> IO ()
ppRes Nil     = printLn ""
ppRes (x::xs) = do
  printLn x
  ppRes xs

ppGraph : GModel -> IO ()
ppGraph g = do
  ppRes (vertices g)
  ppRes (edges g)

runTest : IO ()
runTest = do
    printLn "AA"
    ppGraph amyotModel
