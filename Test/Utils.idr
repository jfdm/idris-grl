module Test.Utils

import GRL.Lang.GLang
import GRL.Eval

import Debug.Trace

%default total
%access public

data TestResults : Type where
  BadModel     : TestResults
  BadResults   : List (GoalNode, SValue, SValue) -> TestResults
  ValidResults : TestResults

getResult : GoalNode -> Strategy -> Maybe (GoalNode, SValue, SValue)
getResult n es =
    let e = getExpSValue n es  in
    let g = getSValue' n       in
      if g == e
        then Nothing
        else Just (n, g, e)
  where
    getSValue' : GoalNode -> SValue
    getSValue' n = fromMaybe NONE (getSValue n)

    getExpectedResult : GoalNode -> Strategy -> Maybe SValue
    getExpectedResult n ss = lookupBy (\x,y => getNodeTitle x == getNodeTitle y) n ss

    getExpSValue : GoalNode -> Strategy -> SValue
    getExpSValue n ss = fromMaybe NONE $ getExpectedResult n ss

collectResults : List GoalNode -> Strategy -> List (GoalNode, SValue, SValue)
collectResults Nil     ss = Nil
collectResults (g::gs) ss =
  case getResult g ss of
    Nothing => collectResults gs ss
    Just x  => x :: collectResults gs ss

partial
execTest : GModel -> Strategy -> Strategy -> TestResults
execTest m s es =
    case (evalModel m (Just s)) of
      BadModel   => BadModel
      Result res => case collectResults res es of
        Nil  => ValidResults
        xs   => BadResults xs

partial
printResults : List (GoalNode, SValue, SValue) -> IO ()
printResults Nil     = pure ()
printResults ((n,g,e)::xs) = do
    putStrLn $ unwords
      [show $ getNodeTitle n , show g, show e]
    printResults xs

partial
doTest : GModel -> Strategy -> Strategy -> IO ()
doTest m s es = do
  case execTest m s es of
    BadModel      => printLn "Bad Model Evaluation"
    ValidResults  => printLn "Test Passed"
    BadResults xs => do
      putStrLn "Tests Failed"
      printResults xs
