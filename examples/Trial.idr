module Trial

import GRL.Lang.Default

-- Service Provider
highPerf : GoalLang ELEM
highPerf = Soft "High Performance" Nothing

lowCost : GoalLang ELEM
lowCost  = Soft "Low Cost" Nothing

minChange : GoalLang ELEM
minChange = Soft "Minimum Changes to Infrastructure" Nothing

maxHardware : GoalLang ELEM
maxHardware = Soft "Maximun Hardware Utilisation" Nothing

highThrough : GoalLang ELEM
highThrough = Soft "High Throughput" Nothing

minMsgEx : GoalLang ELEM
minMsgEx = Soft "Minimum Message Exchange" Nothing

minSwitch : GoalLang ELEM
minSwitch = Soft "Minimum Switch Load" Nothing

-- System

detDataLoc : GoalLang ELEM
detDataLoc = Goal "Determine Data Location" Nothing

dataSCP : GoalLang ELEM
dataSCP = Task "Data in Service Control Point" Nothing

dataNewSNode : GoalLang ELEM
dataNewSNode = Task "Data in New Service Node" Nothing

installSNode : GoalLang ELEM
installSNode = Task "ata in New Service Node" Nothing -- chang

serviceCentralSwitch : GoalLang ELEM
serviceCentralSwitch = Task "Service in Central Switch" Nothing

detSLoc : GoalLang ELEM
detSLoc = Goal "Determine Service Location" Nothing

serviceInSCP : GoalLang ELEM
serviceInSCP = Task "Service in Service Control Point" Nothing

amyotModel : GModel
amyotModel = emptyModel
    \+\ highPerf
    \+\ lowCost
    \+\ minChange
    \+\ maxHardware
    \+\ highThrough
    \+\ minMsgEx
    \+\ minSwitch
    \+\ detDataLoc
    \+\ dataSCP
    \+\ dataNewSNode
    \+\ installSNode
    \+\ serviceCentralSwitch
    \+\ detSLoc
    \+\ serviceInSCP

amyotModel' : GModel
amyotModel' = amyotModel
    \->\ Impacts MAKES minChange lowCost
    \->\ Effects MAKES maxHardware minChange
    \->\ Effects MAKES dataNewSNode minChange
    \->\ Effects MAKES dataSCP minChange
    \->\ Impacts MAKES minMsgEx highThrough
    \->\ Impacts MAKES minSwitch highThrough
    \->\ Impacts SOMENEG serviceInSCP minMsgEx
    \->\ Effects MAKES serviceInSCP minSwitch
    \->\ Effects BREAKS serviceCentralSwitch minSwitch
    \->\ Impacts MAKES serviceCentralSwitch minMsgEx
    \<-\ HasAnd detSLoc      [serviceCentralSwitch, serviceInSCP]
    \<-\ HasIor detSLoc      [dataNewSNode, dataSCP]
    \<-\ HasAnd dataNewSNode [installSNode]
    \<-\ HasAnd highPerf     [maxHardware, highThrough]

namespace Main
   main : IO ()
   main = do
     printLn "AA"
     printLn amyotModel
     printLn $ hasGoal "Service in Service Control Point" amyotModel

     -- res <- run $ genGoalGraph amyotModel
     printLn $ (keys . graph) amyotModel
     putStrLn "\n"
     -- evalModel (keys res) res
     -- print res
