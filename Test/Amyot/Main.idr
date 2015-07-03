-- --------------------------------------------------------------- [ Amyot.idr ]
-- Module    : Amyot.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| The example from Amyot
module Test.Amyot.Main

import GRL.Lang.GLang
import GRL.Eval

import Debug.Trace

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
   \= highPerf
   \= lowCost
   \= minChange
   \= maxHardware
   \= highThrough
   \= minMsgEx
   \= minSwitch
   \= detDataLoc
   \= dataSCP
   \= dataNewSNode
   \= installSNode
   \= serviceCentralSwitch
   \= detSLoc
   \= serviceInSCP
   \= (minChange    ==> lowCost   | MAKES                  )
   \= (maxHardware  ~~> minChange | MAKES                  )
   \= (dataNewSNode ~~> minChange | MAKES                  )
   \= (dataSCP      ~~> minChange | MAKES                  )
   \= (minMsgEx     ==> highThrough | MAKES                )
   \= (minSwitch    ==> highThrough | MAKES                )
   \= (serviceInSCP ==> minMsgEx | SOMENEG                 )
   \= (serviceInSCP         ~~> minSwitch | MAKES          )
   \= (serviceCentralSwitch ~~> minSwitch | BREAK          )
   \= (serviceCentralSwitch ==> minMsgEx  | MAKES          )
   \= (detSLoc      &= [serviceCentralSwitch, serviceInSCP])
   \= (detDataLoc   |= [dataNewSNode, dataSCP]             )
   \= (dataNewSNode |= [installSNode]                      )
   \= (highPerf     |= [maxHardware, highThrough]          )

myFirstStrategy : Strategy
myFirstStrategy = buildStrategy [(detSLoc,SATISFIED)]

-- -------------------------------------------------------------------- [ Test ]
runTest : IO ()
runTest = do
  putStrLn $ prettyModel amyotModel

-- --------------------------------------------------------------------- [ EOF ]
