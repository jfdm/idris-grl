module GRL.Eval.Forward

import Effects
import Effect.State
import Effect.StdIO

import Data.AVL.Dict
import Data.Graph.AList
import Data.Queue
import Data.Stack

import GRL.Model
import GRL.Eval.GenGraph
import GRL.Utils

import GRL.Eval.Qualitative

%access public

-- ----------------------------------------------------- [ Forward Propagation ]

-- data GLink = ALINK | ILINK | XLINK | CLINK Contrib | ELINK Contrib
-- GGraph = Graph (GModel ELEM) (GLink)

||| The effects used in a BFS.
MEvalEffs : List EFFECT
MEvalEffs = [ 'next ::: STATE (Queue Node)
            , 'seen ::: STATE (List Node)
            , 'res  ::: STATE (List (GModel ELEM, EvalVal))
            , STDIO]

{-
1. Get Children
2. Extract decomposition
3. Fold them using specific compare for decomposition
  + AND minimum value presented
  + IOR maximum value set
    + Conflict replaced with Undecided
  + XOR maximum is propogated with warning
4. return result
-}
calcDecomp : Node -> GGraph -> Eff EvalVal MEvalEffs
calcDecomp nval g = do
  let es = getEdges nval g


{-

-}
calcContrib : Node -> GGraph -> EvalVal -> Eff EvalVal MEvalEffs
calcContrib nval g dval = do

evalElem : GModel ELEM -> GGraph  -> Eff EvalVal MEvalEffs
evalElem e g do
  decompValue  <- calcDecomp e
  contribValue <- calcContrib e decompValue
  pure contribValue

private
doModelEval : GGraph -> Eff () MEvalEffs
doModelEval g = do
    q <- 'next :- get
    case popQ q of
      Nothing => pure () -- Stop if all nodes have been traversed
      Just (curr, newQ) => do
        'next :- put newQ

        -- Do the thing we need to do
        printLn curr

        case getValue curr g of
          Nothing  => doModelEval g
          Just val => do
            case isInit val of
              Just
              Nothing => do
        -- Can we eval

        -- Move On
        let es = getSuccs curr g
        doMoves es

        -- Repeat
        doModelEval g
  where
    doMove : Node -> Eff () MEvalEffs
    doMove n = do
      visited <- 'seen :- get
      case List.elem n visited of
        True => pure ()
        False => do
          'seen :- update (\xs => [n] ++ xs)
          'next :- update (\xs => pushQ n xs)

    doMoves : Maybe (List Node) -> Eff () MEvalEffs
    doMoves Nothing    = pure ()
    doMoves (Just Nil) = pure ()
    doMoves (Just (e::es)) = do
      doMove e
      doMoves (Just es)

evalModel : List Nat -> GGraph -> IO ()
evalModel ns g = runInit [ 'next := pushQThings ns mkQueue
                         , 'seen := List.Nil
                         , 'res := List.Nil
                         , ()
                         ] $ doModelEval g

-- --------------------------------------------------------------------- [ EOF ]
