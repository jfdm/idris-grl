-- --------------------------------------------------------------- [ Utils.idr ]
-- Module    : Utils.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Utils

import Data.GraphViz.SimpleDot

import GRL.Common
import GRL.Model

toSimpleDot : GModel -> SimpleDot GRAPH
toSimpleDot g = Digraph (nodes (verticesID g)) (edges' (edges g))
  where

    f : NodeID -> String
    f n = case getValueByID n g of
        Nothing => ""
        Just u  => getNodeTitle u

    nodes : List NodeID -> List (SimpleDot NODE)
    nodes vs = map (\x => Node (x) [("label", (f x))]) vs

    convEdge : Edge GoalEdge -> SimpleDot EDGE
    convEdge (x,y, Nothing)     = Edge (y) (x) Nil
    convEdge (x,y, Just Decomp) = Edge (y) (x) [("label", "Decomp FIX")]
    convEdge (x,y, Just (Contribution l)) = Edge (x) (y) [("label", "Impacts " ++ show l)]
    convEdge (x,y, Just (Correlation  l)) = Edge (x) (y) [("label", "Affects " ++ show l)]

    edges' : List (Edge GoalEdge) -> List (SimpleDot EDGE)
    edges' es = map (convEdge) es

-- --------------------------------------------------------------------- [ EOF ]
