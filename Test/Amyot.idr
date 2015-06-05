module Test.Amyot

import GRL.Lang.Default
import GRL.Eval

-- Service Provider
highPerf : GoalLang ELEM
highPerf = Soft "High Performance" Nothing

lowCost : GoalLang ELEM
lowCost  = Soft "Low Cost" Nothing

minChange : GoalLang ELEM
minChange = Soft "Minimum Changes to Infrastructure" Nothing

maxHardware : GoalLang ELEM
maxHardware = Soft "Maximun Hardware Utilisation" (Just WEAKSATIS)

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
dataSCP = Task "Data in Service Control Point" (Just SATISFIED)

dataNewSNode : GoalLang ELEM
dataNewSNode = Task "Data in New Service Node" Nothing

installSNode : GoalLang ELEM
installSNode = Task "Install Service Node" Nothing -- chang

serviceCentralSwitch : GoalLang ELEM
serviceCentralSwitch = Task "Service in Central Switch" Nothing

detSLoc : GoalLang ELEM
detSLoc = Goal "Determine Service Location" Nothing

serviceInSCP : GoalLang ELEM
serviceInSCP = Task "Service in Service Control Point" (Just SATISFIED)

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
    \->\ Effects BREAK serviceCentralSwitch minSwitch
    \->\ Impacts MAKES serviceCentralSwitch minMsgEx
    \<-\ HasAnd detSLoc      [serviceCentralSwitch, serviceInSCP]
    \<-\ HasIor detSLoc      [dataNewSNode, dataSCP]
    \<-\ HasAnd dataNewSNode [installSNode]
    \<-\ HasAnd highPerf     [maxHardware, highThrough]



ppRes : Show a => List (a) -> IO ()
ppRes Nil     = printLn ""
ppRes (x::xs) = do
  printLn x
  ppRes xs

ppGraph : GModel -> IO ()
ppGraph g = do
  ppRes (vertices g)
  ppRes (edges g)

runTest : IO ()
runTest = do
  printLn "AA"

  case validInit amyotModel' of
    False => do
      putStrLn "Wrongly init'd model."
      ppGraph amyotModel'
--      printLn amyotModel'

    True  => do
      ppGraph amyotModel'
      ppRes $ evalModel amyotModel'
