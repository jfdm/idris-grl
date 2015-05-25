module Trial

-- import Effects
-- import Effect.State
-- import Effect.StdIO

import Data.AVL.Dict
import Data.Graph.AList
import Data.Queue
import Data.Stack

import GRL.Model
-- import GRL.Eval.GenGraph
-- import GRL.Eval.Forward

namespace Amyot2010agm
-- Service Provider
  highPerf : GModel ELEM
  highPerf = soft "High Performance" Nothing

  lowCost : GModel ELEM
  lowCost  = soft "Low Cost" Nothing

  minChange : GModel ELEM
  minChange = soft "Minimum Changes to Infrastructure" Nothing

  maxHardware : GModel ELEM
  maxHardware = soft "Maximun Hardware Utilisation" Nothing

  highThrough : GModel ELEM
  highThrough = soft "High Throughput" Nothing

  minMsgEx : GModel ELEM
  minMsgEx = soft "Minimum Message Exchange" Nothing

  minSwitch : GModel ELEM
  minSwitch = soft "Minimum Switch Load" Nothing

-- System

  detDataLoc : GModel ELEM
  detDataLoc = goal "Determine Data Location" Nothing

  dataSCP : GModel ELEM
  dataSCP = task "Data in Service Control Point" Nothing

  dataNewSNode : GModel ELEM
  dataNewSNode = task "Data in New Service Node" Nothing

  installSNode : GModel ELEM
  installSNode = task "Data in New Service Node" Nothing

  serviceCentralSwitch : GModel ELEM
  serviceCentralSwitch = task "Service in Central Switch" Nothing

  detSLoc : GModel ELEM
  detSLoc = goal "Determine Service Location" Nothing

  serviceInSCP : GModel ELEM
  serviceInSCP = task "Service in Service Control Point" Nothing

  amyotModel : GModel MODEL
  amyotModel = with List emptyModel
      /+/ highPerf
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

      /+>/ impacts MAKES minChange lowCost
      /+>/ effects MAKES maxHardware minChange
      /+>/ effects MAKES dataNewSNode minChange
      /+>/ effects MAKES dataSCP minChange
      /+>/ impacts MAKES minMsgEx highThrough
      /+>/ impacts MAKES minSwitch highThrough
      /+>/ impacts SOMENEG serviceInSCP minMsgEx
      /+>/ effects MAKES serviceInSCP minSwitch
      /+>/ effects BREAKS serviceCentralSwitch minSwitch
      /+>/ impacts MAKES serviceCentralSwitch minMsgEx
      /+</ and detSLoc [serviceCentralSwitch, serviceInSCP]
      /+</ ior detDataLoc [dataNewSNode, dataSCP]
      /+</ and dataNewSNode [installSNode]
      /+</ and highPerf [maxHardware, highThrough]


namespace Main
  main : IO ()
  main = putStrLn $ show amyotModel
    -- res <- run $ genGoalGraph amyotModel
    -- print $ keys res
    -- putStrLn "\n"
    -- evalModel (keys res) res
    -- print res
