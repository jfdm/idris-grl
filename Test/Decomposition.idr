-- ----------------------------------------------------------------- [ IOR.idr ]
-- Module    : IOR.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Testing IOR contribution evaluation
module Test.Decomposition

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

or_b : Strategy
or_b = buildStrategy [(lan, WEAKDEN), (wireless, WEAKDEN), (internet, WEAKDEN)]

or_c : Strategy
or_c = buildStrategy [(lan, CONFLICT), (wireless, WEAKSATIS), (internet, WEAKDEN)]

or_d : Strategy
or_d = buildStrategy [(lan, CONFLICT), (wireless, SATISFIED), (internet, WEAKDEN)]

-- ---------------------------------------------------------- [ AND Strategies ]

and_a : Strategy
and_a = buildStrategy [(lan, NONE), (wireless, WEAKSATIS), (internet, WEAKDEN)]

and_b : Strategy
and_b = buildStrategy [(lan, SATISFIED), (wireless, SATISFIED), (internet, SATISFIED)]

and_c : Strategy
and_c = buildStrategy [(lan, CONFLICT), (wireless, WEAKSATIS), (internet, WEAKDEN)]

and_d : Strategy
and_d = buildStrategy [(lan, CONFLICT), (wireless, WEAKSATIS), (internet, DENIED)]

-- -------------------------------------------------------------------- [ Test ]

partial
doTest : GModel -> Maybe Strategy -> IO ()
doTest m s = do
  let res = evalModel m s
  case List.find (\x => getNodeTitle x == "Connection") res of
    Nothing => printLn "oopsie"
    Just x  => printLn $ getSValue x

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

  putStrLn "Strategy A: expecting WeaklySatisfied"
  doTest modelIOR (Just or_a)

  putStrLn "Strategy B: expecting WeaklyDenied"
  doTest modelIOR (Just or_b)

  putStrLn "Strategy C: expecting UNKNOWN"
  doTest modelIOR (Just or_c)

  putStrLn "Strategy D: expecting SATISFIED"
  doTest modelIOR (Just or_d)

  putStrLn "--> AND"


  putStrLn "Strategy A: expecting WeaklyDenied"
  doTest modelAND (Just and_a)

  putStrLn "Strategy B: expecting Satisfied"
  doTest modelAND (Just and_b)

  putStrLn "Strategy C: expecting UNKNOWN"
  doTest modelAND (Just and_c)

  putStrLn "Strategy D: expecting Denied"
  doTest modelAND (Just and_d)

-- --------------------------------------------------------------------- [ EOF ]
