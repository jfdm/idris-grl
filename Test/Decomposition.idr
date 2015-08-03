-- ----------------------------------------------------------------- [ IOR.idr ]
-- Module    : IOR.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Testing IOR contribution evaluation
module Test.Decomposition

import GRL.Lang.GLang
import GRL.Eval

import Test.Utils

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

modelIOR : GModel
modelIOR = emptyModel
   \= conn \= lan \= wireless \= internet
   \= conn |= [lan,wireless,internet]

modelAND : GModel
modelAND = emptyModel
   \= conn \= lan \= wireless \= internet
   \= conn &= [lan,wireless,internet]

-- ---------------------------------------------------------- [ IOR Strategies ]

or_a : Strategy
or_a = buildStrategy [(lan, NONE), (wireless, WEAKSATIS), (internet, WEAKDEN)]

or_a' : Strategy
or_a' = buildStrategy [(conn,WEAKSATIS), (lan, NONE), (wireless, WEAKSATIS), (internet, WEAKDEN)]


or_b : Strategy
or_b = buildStrategy [(lan, WEAKDEN), (wireless, WEAKDEN), (internet, WEAKDEN)]

or_b' : Strategy
or_b' = buildStrategy [(conn,WEAKDEN), (lan, WEAKDEN), (wireless, WEAKDEN), (internet, WEAKDEN)]


or_c : Strategy
or_c = buildStrategy [(lan, CONFLICT), (wireless, WEAKSATIS), (internet, WEAKDEN)]

or_c' : Strategy
or_c' = buildStrategy [(conn,UNDECIDED), (lan, CONFLICT), (wireless, WEAKSATIS), (internet, WEAKDEN)]

or_d : Strategy
or_d = buildStrategy [(lan, CONFLICT), (wireless, SATISFIED), (internet, WEAKDEN)]

or_d' : Strategy
or_d' = buildStrategy [(conn,SATISFIED), (lan, CONFLICT), (wireless, SATISFIED), (internet, WEAKDEN)]

-- ---------------------------------------------------------- [ AND Strategies ]

and_a : Strategy
and_a = buildStrategy [(lan, NONE), (wireless, WEAKSATIS), (internet, WEAKDEN)]

and_a' : Strategy
and_a' = buildStrategy [(conn, WEAKDEN), (lan, NONE), (wireless, WEAKSATIS), (internet, WEAKDEN)]

and_b : Strategy
and_b = buildStrategy [(lan, SATISFIED), (wireless, SATISFIED), (internet, SATISFIED)]

and_b' : Strategy
and_b' = buildStrategy [(conn,SATISFIED), (lan, SATISFIED), (wireless, SATISFIED), (internet, SATISFIED)]

and_c : Strategy
and_c = buildStrategy [(lan, CONFLICT), (wireless, WEAKSATIS), (internet, WEAKDEN)]

and_c' : Strategy
and_c' = buildStrategy [(conn,UNDECIDED), (lan, CONFLICT), (wireless, WEAKSATIS), (internet, WEAKDEN)]

and_d : Strategy
and_d = buildStrategy [(lan, CONFLICT), (wireless, WEAKSATIS), (internet, DENIED)]

and_d' : Strategy
and_d' = buildStrategy [(conn,DENIED), (lan, CONFLICT), (wireless, WEAKSATIS), (internet, DENIED)]

-- -------------------------------------------------------------------- [ Test ]

partial
runTest : IO ()
runTest = do
  putStrLn "--> Decomposition Tests"
  printLn $ True == and [ WEAKDEN   == getDecompAnd [WEAKDEN,WEAKSATIS,NONE]
                        , SATISFIED == getDecompAnd [SATISFIED,SATISFIED,SATISFIED]
                        , UNDECIDED == getDecompAnd [WEAKDEN,WEAKSATIS,CONFLICT]
                        , DENIED    == getDecompAnd [DENIED,WEAKSATIS,CONFLICT]
                        ]

  printLn $ True == and [ WEAKSATIS == getDecompIOR [WEAKDEN,WEAKSATIS,NONE]
                        , WEAKDEN   == getDecompIOR [WEAKDEN,WEAKDEN,WEAKDEN]
                        , UNDECIDED == getDecompIOR [WEAKDEN,WEAKSATIS,CONFLICT]
                        , SATISFIED == getDecompIOR [WEAKDEN,SATISFIED,CONFLICT]
                        ]

  putStrLn "--> IOR"

  putStrLn "Strategy A:"
  doTest modelIOR or_a or_a'

  putStrLn "Strategy B:"
  doTest modelIOR or_b or_b'

  putStrLn "Strategy C:"
  doTest modelIOR or_c or_c'

  putStrLn "Strategy D:"
  doTest modelIOR or_d or_d'

  putStrLn "--> AND"


  putStrLn "Strategy A:"
  doTest modelAND and_a and_a'

  putStrLn "Strategy B:"
  doTest modelAND and_b and_b'

  putStrLn "Strategy C:"
  doTest modelAND and_c and_c'

  putStrLn "Strategy D:"
  doTest modelAND and_d and_d'

-- --------------------------------------------------------------------- [ EOF ]
