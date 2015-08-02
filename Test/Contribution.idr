-- ----------------------------------------------------------------- [ IOR.idr ]
-- Module    : IOR.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Testing IOR contribution evaluation
module Test.Contribution

import GRL.Lang.GLang
import GRL.Eval

%access public
%default total

-- -------------------------------------------------------- [ Model Definition ]

conn : GOAL
conn = mkGoal "Increase Mobility"

lan : TASK
lan = mkTask "LAN"

wireless : TASK
wireless = mkTask "Wireless"

internet : TASK
internet = mkTask "Internet"

model : GModel
model = emptyModel
   \= conn \= lan \= wireless \= internet
   \= (internet ==> conn | SOMEPOS)
   \= (wireless ==> conn | MAKES)
   \= (lan      ==> conn | SOMENEG)

-- ---------------------------------------------------------- [ IOR Strategies ]

a : Strategy
a = buildStrategy [(lan, NONE), (wireless, WEAKSATIS), (internet, WEAKDEN)]

b : Strategy
b = buildStrategy [(lan, NONE), (wireless, WEAKSATIS), (internet, WEAKSATIS)]

-- -------------------------------------------------------------------- [ Test ]

partial
doTest : GModel -> Maybe Strategy -> IO ()
doTest m s = do
  let res = evalModel m s
  case List.find (\x => getNodeTitle x == "Increase Mobility") res of
    Nothing => printLn "oopsie"
    Just x  => printLn $ getSValue x

partial
runTest : IO ()
runTest = do
  putStrLn "--> Composition Tests"

  putStrLn "Strategy A: expecting None"
  doTest model (Just a)

  putStrLn "Strategy B: expected Weakly Satisfied"
  doTest model (Just b)

-- --------------------------------------------------------------------- [ EOF ]
