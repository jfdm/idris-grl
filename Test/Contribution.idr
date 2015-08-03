-- ----------------------------------------------------------------- [ IOR.idr ]
-- Module    : IOR.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Testing IOR contribution evaluation
module Test.Contribution

import GRL.Lang.GLang
import GRL.Eval

import Test.Utils

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
a = buildStrategy
    [ (lan, NONE)
    , (wireless, WEAKSATIS)
    , (internet, WEAKDEN)]

aExpRes : Strategy
aExpRes = buildStrategy
    [ (conn, NONE)
    , (lan, NONE)
    , (wireless, WEAKSATIS)
    , (internet, WEAKDEN)]

b : Strategy
b = buildStrategy
    [ (lan, NONE)
    , (wireless, WEAKSATIS)
    , (internet, WEAKSATIS)]

bExpRes : Strategy
bExpRes = buildStrategy
    [ (lan, NONE)
    , (wireless, WEAKSATIS)
    , (internet, WEAKSATIS)
    , (conn, WEAKSATIS)]

-- -------------------------------------------------------------------- [ Test ]

partial
runTest : IO ()
runTest = do
  putStrLn "--> Composition Tests"

  putStrLn "Strategy A:"
  doTest model a aExpRes

  putStrLn "Strategy B:"
  doTest model b bExpRes

-- --------------------------------------------------------------------- [ EOF ]
