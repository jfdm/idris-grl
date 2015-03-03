module GRL.Eval.GenGraph

import Effects
import Effect.State

import Data.AVL.Dict
import Data.Graph.AList

import GRL.Model

||| Links in a goal graph.
data GLink = ALINK | ILINK | XLINK | CLINK Contrib | ELINK Contrib

instance Show GLink where
  show ALINK = "And"
  show ILINK = "IOR"
  show XLINK = "XOR"
  show (CLINK c) = "Contribution " ++ show c
  show (ELINK c) = "SideEffect " ++ show c

||| A goal graph is a graph of nodes and links...
GGraph : Type
GGraph = Graph (GModel ELEM) (GLink)

||| State used for keeping track of node and their ids
GGEffs : List EFFECT
GGEffs = [STATE (List (GModel ELEM, Nat))]

assignNodeID : List (GModel ELEM) -> (List (GModel ELEM, Nat))
assignNodeID = doAssign Z
  where
    doAssign : Nat -> List (GModel ELEM) -> (List (GModel ELEM, Nat))
    doAssign id Nil     = Nil
    doAssign id (e::es) = (e, id) :: doAssign (S id) es

getID : GModel ELEM -> {GGEffs} Eff $ Maybe Nat
getID e = pure $ lookup e !get

genLink : GLink
        -> GModel ELEM
        -> GModel ELEM
        -> {GGEffs} Eff $ Maybe (LEdge GLink)
genLink lval ex ey = do
  x <- getID ex
  y <- getID ey
  case (x,y) of
    (Just x', Just y' ) => pure $ Just (x', y', lval)
    otherwise           => pure Nothing

genGLink : GModel LINK -> {GGEffs} Eff $ List (Maybe (LEdge GLink))
genGLink (Impacts c a b) = pure [!(genLink (CLINK c) b a)] -- for graph traversal
genGLink (Effects c a b) = pure [!(genLink (ELINK c) b a)]
genGLink (AND x ys)      = mapE (genLink ALINK x) ys
genGLink (IOR x ys)      = mapE (genLink ILINK x) ys
genGLink (XOR x ys)      = mapE (genLink XLINK x) ys

genGLinks : List (GModel LINK) -> {GGEffs} Eff $ List (LEdge GLink)
genGLinks ls = do
  lls <- mapE genGLink ls
  pure $ mapMaybe id (concat lls)


genGoalGraph : GModel MODEL -> {GGEffs} Eff GGraph
genGoalGraph (GRLSpec es ls) = do
  let es' = assignNodeID es
  put es'
  let g = addNodes (map (\(x,y) => (y,x)) es') Empty
  ls' <- genGLinks ls
  pure $ addEdges ls' g


-- --------------------------------------------------------------------- [ EOF ]
