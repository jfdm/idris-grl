||| Evaluation Strategies
module GRL.Eval.Strategy

import GRL.Common
import GRL.IR
import GRL.Builder
import GRL.Model

||| Strategies are just list of node evaluation pairings.
Strategy : Type
Strategy = List (GoalNode, Satisfaction)

buildStrategy : GRL expr => List (expr ELEM, Satisfaction) -> Strategy
buildStrategy es = map (\(e,v) => ((convExpr . mkGoal) e, v)) es

||| Deploy Strategy being careful not to override default values, returning a pairing of the modified model, and original.
deployStrategy : GModel -> Strategy -> (GModel, GModel)
deployStrategy oldG ss = (newG, oldG)
  where
    canUp : Satisfaction -> GoalNode -> GoalNode
    canUp s n = if isJust (sValue n)
                  then n
                  else record {sValue = Just s} n

    doUp : (GoalNode, Satisfaction) -> GModel -> GModel
    doUp (n,s) m = updateGoalNode (\x => gTitle n == gTitle x )
                                  (canUp s)
                                  m

    newG : GModel
    newG = foldl (flip doUp) oldG ss
