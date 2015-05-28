module Trial

import GRL.Lang

-- Service Provider
highPerf : GRLExpr ELEM
highPerf = soft "High Performance" Nothing

lowCost : GRLExpr ELEM
lowCost  = soft "Low Cost" Nothing

minChange : GRLExpr ELEM
minChange = soft "Minimum Changes to Infrastructure" Nothing

maxHardware : GRLExpr ELEM
maxHardware = soft "Maximun Hardware Utilisation" Nothing

highThrough : GRLExpr ELEM
highThrough = soft "High Throughput" Nothing

minMsgEx : GRLExpr ELEM
minMsgEx = soft "Minimum Message Exchange" Nothing

minSwitch : GRLExpr ELEM
minSwitch = soft "Minimum Switch Load" Nothing

-- System

detDataLoc : GRLExpr ELEM
detDataLoc = goal "Determine Data Location" Nothing

dataSCP : GRLExpr ELEM
dataSCP = task "Data in Service Control Point" Nothing

dataNewSNode : GRLExpr ELEM
dataNewSNode = task "Data in New Service Node" Nothing

installSNode : GRLExpr ELEM
installSNode = task "ata in New Service Node" Nothing -- chang

serviceCentralSwitch : GRLExpr ELEM
serviceCentralSwitch = task "Service in Central Switch" Nothing

detSLoc : GRLExpr ELEM
detSLoc = goal "Determine Service Location" Nothing

serviceInSCP : GRLExpr ELEM
serviceInSCP = task "Service in Service Control Point" Nothing

amyotModel : GModel
amyotModel = emptyModel
  /+/ highPerf
  /+/ lowCost
  /+/ lowCost
  /+/ minChange
  /+/ maxHardware
  /+/ highThrough
  /+/ minMsgEx
  /+/ minSwitch
  /+/ detDataLoc
  /+/ dataSCP
  /+/ dataNewSNode
  /+/ installSNode
  /+/ serviceCentralSwitch
  /+/ detSLoc
  /+/ serviceInSCP
  -- /+/ impacts MAKES minChange lowCost
  -- /+/ effects MAKES maxHardware minChange
  -- /+/ effects MAKES dataNewSNode minChange
  -- /+/ effects MAKES dataSCP minChange
  -- /+/ impacts MAKES minMsgEx highThrough
  -- /+/ impacts MAKES minSwitch highThrough
  -- /+/ impacts SOMENEG serviceInSCP minMsgEx
  -- /+/ effects MAKES serviceInSCP minSwitch
  -- /+/ effects BREAKS serviceCentralSwitch minSwitch
  -- /+/ impacts MAKES serviceCentralSwitch minMsgEx
  -- /+/ and detSLoc [serviceCentralSwitch, serviceInSCP]
  -- /+/ ior detSLoc [dataNewSNode, dataSCP]
  -- /+/ and dataNewSNode [installSNode]
  -- /+/ and highPerf [maxHardware, highThrough]

namespace Main
   main : IO ()
   main = do
     printLn amyotModel
     printLn $ hasGoal "Service" amyotModel

--     -- res <- run $ genGoalGraph amyotModel
--     -- print $ keys res
--     -- putStrLn "\n"
--     -- evalModel (keys res) res
--     -- print res
