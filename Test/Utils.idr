module Test.Utils

import GRL.Lang.GLang
import GRL.Eval

import Debug.Trace

%default total
%access public


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
execTest : GModel -> Strategy -> Strategy -> List (GoalNode, SValue, SValue)
execTest m s es = collectResults (evalModel m (Just s)) es

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
  let res = execTest m s es
  case res of
    Nil => printLn "Test Passed"
    xs  => do
      putStrLn "Tests Failed"
      printResults xs
