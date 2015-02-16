module GRL.Eval.GenGraph

import Effects
import Effect.State

import Data.Graph.AList

GGEffs : List EFFECT
GGEffs = [STATE (Graph (GModel ELEM) (GModel LINK))]

insertGoal : Nat -> List ((GModel ELEM) -> {GGEffs} Eff ()
insertGoal n Nil     = pure ()
insertGoal n (e::es) = do
  gg <- get
  addNode (n,e) gg
  insertGoal (S n) es gg
  put gg

insertEdge : List (GModel ELEM) -> {GGEffs} Eff ()
insertEdge (DecompAND a bs) =

genGoalGraph : GModel MODEL -> {GGEffs} Eff ()
genGoalGraph (GRLSpec as es ls) = do
   gg <- get
   insertGoals Z es
   let gg'' = foldr genGoalGraph gg' ls
   pure ()
genGoalGraph (Go)
