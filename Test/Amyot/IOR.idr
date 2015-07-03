-- ----------------------------------------------------------------- [ IOR.idr ]
-- Module    : IOR.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Testing IOR contribution evaluation
module Test.Amyot.IOR

import GRL.Lang.GLang
import GRL.Eval

%access public
%default total

-- -------------------------------------------------------- [ Model Definition ]

conn : GOAL
conn = mkGoal "Connection"

lan : TASK
lan = mkTask "LAN"

wireless : TASK
wireless = mkTask "Wireless"

internet : TASK
internet = mkTask "Internet"

model : GModel
model = emptyModel
   \= conn \= lan \= wireless \= internet
   \= conn |= [lan,wireless,internet]

-- -------------------------------------------------------------- [ Strategies ]

a : Strategy
a = buildStrategy [(lan, UNKNOWN), (wireless, WEAKSATIS), (internet, DENIED)]

b : Strategy
b = buildStrategy [(lan, DENIED), (wireless, DENIED), (internet, DENIED)]

c : Strategy
c = buildStrategy [(lan, CONFLICT), (wireless, WEAKSATIS), (internet, DENIED)]

d : Strategy
d = buildStrategy [(lan, CONFLICT), (wireless, SATISFIED), (internet, DENIED)]

-- -------------------------------------------------------------------- [ Test ]

partial
runTest : IO ()
runTest = do
  putStrLn "Testing IOR"
  putStrLn $ prettyModel model

  putStrLn "Strategy A"
  printLn $ evalModel model (Just a)

  putStrLn "Strategy B"
  printLn $ evalModel model (Just b)

  putStrLn "Strategy C"
  printLn $ evalModel model (Just c)

  putStrLn "Strategy D"
  printLn $ evalModel model (Just d)

-- --------------------------------------------------------------------- [ EOF ]
