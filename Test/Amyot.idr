-- --------------------------------------------------------------- [ Amyot.idr ]
-- Module    : Amyot.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| The example from Amyot
module Test.Amyot

import GRL.Lang.GLang
import GRL.Eval

import Test.Utils

%default total
%access public

-- ------------------------------------------------------------------- [ Nodes ]

-- Service Provider
highPerf : SOFT
highPerf = mkSoft "High Performance"

lowCost : SOFT
lowCost  = mkSoft "Low Cost"

minChange : SOFT
minChange = mkSoft "Minimum Changes to Infrastructure"

maxHardware : SOFT
maxHardware = mkSoft "Maximun Hardware Utilisation"

highThrough : SOFT
highThrough = mkSoft "High Throughput"

minMsgEx : SOFT
minMsgEx = mkSoft "Minimum Message Exchange"

minSwitch : SOFT
minSwitch = mkSoft "Minimum Switch Load"

-- System

detDataLoc : GOAL
detDataLoc = mkGoal "Determine Data Location"

dataSCP : TASK
dataSCP = mkTask "Data in Service Control Point"

dataNewSNode : TASK
dataNewSNode = mkTask "Data in New Service Node"

installSNode : TASK
installSNode = mkTask "Install Service Node"  -- chang

serviceCentralSwitch : TASK
serviceCentralSwitch = mkTask "Service in Central Switch"

detSLoc : GOAL
detSLoc = mkGoal "Determine Service Location"

serviceInSCP : TASK
serviceInSCP = mkTask "Service in Service Control Point"

-- ------------------------------------------------------------------- [ Model ]
amyotModel : GModel
amyotModel = emptyModel
   \= highPerf               --  0
   \= lowCost                --  1
   \= minChange              --  2
   \= maxHardware            --  3
   \= highThrough            --  4
   \= minMsgEx               --  5
   \= minSwitch              --  6
   \= detDataLoc             --  7
   \= dataSCP                --  8
   \= dataNewSNode           --  9
   \= installSNode           -- 10
   \= serviceCentralSwitch   -- 11
   \= detSLoc                -- 12
   \= serviceInSCP           -- 13
   \= (minChange    ==> lowCost   | HELPS                  )
   \= (maxHardware  ~~> minChange | HELPS                  )
   \= (dataNewSNode ~~> minChange | HURTS                  )
   \= (dataSCP      ~~> minChange | HELPS                  )
   \= (minMsgEx     ==> highThrough | SOMEPOS              )
   \= (minSwitch    ==> highThrough | HELPS                )
   \= (serviceInSCP ==> minMsgEx | SOMENEG                 )
   \= (serviceInSCP ~~> minSwitch | MAKES                  )
   \= (serviceCentralSwitch ==> minMsgEx  | MAKES          )
   \= (serviceCentralSwitch ~~> minSwitch | BREAK          )
   \= (detSLoc      |= [serviceCentralSwitch, serviceInSCP])
   \= (detDataLoc   |= [dataNewSNode, dataSCP]             )
   \= (dataNewSNode &= [installSNode]                      )
   \= (highPerf     &= [maxHardware, highThrough]          )

-- ---------------------------------------------------------------- [ Strategy ]

strategy1 : Strategy
strategy1 = buildStrategy [ (maxHardware, WEAKSATIS)
                          , (dataSCP, SATISFIED)
                          , (serviceCentralSwitch, SATISFIED)]

strategy1ExpectedResults : Strategy
strategy1ExpectedResults = buildStrategy
    [ (lowCost,              WEAKSATIS)
    , (minChange,            WEAKSATIS)
    , (detDataLoc,           SATISFIED)
    , (highPerf,             NONE)
    , (maxHardware,          WEAKSATIS)
    , (highThrough,          NONE)
    , (minMsgEx,             SATISFIED)
    , (minSwitch,            DENIED)
    , (dataSCP,              SATISFIED)
    , (dataNewSNode,         NONE)
    , (installSNode,         NONE)
    , (serviceCentralSwitch, SATISFIED)
    , (detSLoc,              SATISFIED)
    , (serviceInSCP,         NONE)]

-- ---------------------------------------------------------------- [ Strategy ]

strategy2 : Strategy
strategy2 = buildStrategy
    [ (maxHardware, WEAKSATIS)
    , (serviceCentralSwitch, SATISFIED)
    , (installSNode, SATISFIED)]

strategy2ExpectedResults : Strategy
strategy2ExpectedResults = buildStrategy
    [ (lowCost,              NONE)
    , (minChange,            NONE)
    , (detDataLoc,           SATISFIED)
    , (highPerf,             NONE)
    , (maxHardware,          WEAKSATIS)
    , (highThrough,          NONE)
    , (minMsgEx,             SATISFIED)
    , (minSwitch,            DENIED)
    , (dataSCP,              NONE)
    , (dataNewSNode,         SATISFIED)
    , (installSNode,         SATISFIED)
    , (serviceCentralSwitch, SATISFIED)
    , (detSLoc,              SATISFIED)
    , (serviceInSCP,         NONE)]

-- ---------------------------------------------------------------- [ Strategy ]

strategy4 : Strategy
strategy4 = buildStrategy
    [ (maxHardware, WEAKSATIS)
    , (dataSCP, SATISFIED)
    , (serviceInSCP, SATISFIED)]

strategy4ExpectedResults : Strategy
strategy4ExpectedResults = buildStrategy
    [ (lowCost,              WEAKSATIS)
    , (minChange,            WEAKSATIS)
    , (detDataLoc,           SATISFIED)
    , (highPerf,             NONE)
    , (maxHardware,          WEAKSATIS)
    , (highThrough,          NONE)
    , (minMsgEx,             WEAKDEN)
    , (minSwitch,            SATISFIED)
    , (dataSCP,              SATISFIED)
    , (dataNewSNode,         NONE)
    , (installSNode,         NONE)
    , (serviceCentralSwitch, NONE)
    , (detSLoc,              SATISFIED)
    , (serviceInSCP,         SATISFIED)]



-- -------------------------------------------------------------------- [ Test ]
partial
runTest : IO ()
runTest = do
  putStrLn "--> Amyot 2010 gem"

  putStrLn "Strategy 1:"
  doTest amyotModel strategy1 strategy1ExpectedResults

  putStrLn "Strategy 2:"
  doTest amyotModel strategy2 strategy2ExpectedResults

  putStrLn "Strategy 3: Not Cannot be replicated"

  putStrLn "Strategy 4:"
  doTest amyotModel strategy4 strategy4ExpectedResults

  putStrLn "Strategy 5: Not Cannot be replicated"
  putStrLn "Strategy 6: Not Cannot be replicated"


-- --------------------------------------------------------------------- [ EOF ]
