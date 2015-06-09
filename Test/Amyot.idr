module Test.Amyot

import GRL.Lang.GLang
import GRL.Eval

import Debug.Trace

-- Service Provider
highPerf : SOFT
highPerf = MkSoft "High Performance" Nothing

lowCost : SOFT
lowCost  = MkSoft "Low Cost" Nothing

minChange : SOFT
minChange = MkSoft "Minimum Changes to Infrastructure" Nothing

maxHardware : SOFT
maxHardware = MkSoft "Maximun Hardware Utilisation" (Just WEAKSATIS)

highThrough : SOFT
highThrough = MkSoft "High Throughput" Nothing

minMsgEx : SOFT
minMsgEx = MkSoft "Minimum Message Exchange" Nothing

minSwitch : SOFT
minSwitch = MkSoft "Minimum Switch Load" Nothing

-- System

detDataLoc : GOAL
detDataLoc = MkGoal "Determine Data Location" Nothing

dataSCP : TASK
dataSCP = MkTask "Data in Service Control Point" (Just SATISFIED)

dataNewSNode : TASK
dataNewSNode = MkTask "Data in New Service Node" Nothing

installSNode : TASK
installSNode = MkTask "Install Service Node" Nothing -- chang

serviceCentralSwitch : TASK
serviceCentralSwitch = MkTask "Service in Central Switch" Nothing

detSLoc : GOAL
detSLoc = MkGoal "Determine Service Location" Nothing

serviceInSCP : TASK
serviceInSCP = MkTask "Service in Service Control Point" (Just SATISFIED)

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
   \= (detSLoc      |= [dataNewSNode, dataSCP]             )
   \= (dataNewSNode |= [installSNode]                      )
   \= (highPerf     |= [maxHardware, highThrough]          )

myFirstStrategy : Strategy
myFirstStrategy = buildStrategy [(detSLoc,SATISFIED)]


-- runTest : IO ()
-- runTest = do
--   printLn "AA"

--   case validInit amyotModel of
--     False => do
--       putStrLn "Wrongly init'd model."
--       ppGraph amyotModel
-- --      printLn amyotModel'

--     True  => do
--       ppGraph amyotModel
--       let (s,o) = deployStrategy amyotModel myFirstStrategy
--       ppRes $ evalModel s
