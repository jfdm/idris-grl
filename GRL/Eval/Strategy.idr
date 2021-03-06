-- ------------------------------------------------------------ [ Strategy.idr ]
-- Module    : Strategy.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Evaluation Strategies
module GRL.Eval.Strategy

import GRL.Common
import GRL.IR
import GRL.Builder
import GRL.Model

||| Strategies are just list of node evaluation pairings.
public export
Strategy : Type
Strategy = List (GoalNode, SValue)

export
buildStrategy : GRL expr => List (expr ELEM, SValue) -> Strategy
buildStrategy es = map (\(e,v) => ((convExpr . mkElem) e, v)) es

||| Deploy Strategy being careful not to override default values, returning a pairing of the modified model, and original.
export
deployStrategy : GModel -> Strategy -> (GModel, GModel)
deployStrategy oldG ss = (newG, oldG)
  where
    canUp : SValue -> GoalNode -> GoalNode
    canUp s n = record {getSValue = Just s} n

    doUp : (GoalNode, SValue) -> GModel -> GModel
    doUp (n,s) m = updateGoalNode (\x => getNodeTitle n == getNodeTitle x )
                                  (canUp s)
                                  m

    newG : GModel
    newG = foldr (doUp) oldG ss

-- --------------------------------------------------------------------- [ EOF ]
