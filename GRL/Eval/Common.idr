-- -------------------------------------------------------------- [ Common.idr ]
-- Module    : Common.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Eval.Common

import GRL.Common
import GRL.Model


-- ------------------------------------------------------------- [ Eval Result ]

namespace EvalResult
  data EvalResult : Type where
    Result   : List GoalNode  -> EvalResult
    BadModel : EvalResult

  instance Show EvalResult where
    show BadModel    = "Bad Model"
    show (Result xs) = unlines $ map (mkPretty) xs
       where
         mkPretty : GoalNode -> String
         mkPretty x = unwords [getNodeTitle x, show (fromMaybe NONE (getSValue x)), "\n"]


  toString : EvalResult -> (GoalNode -> String) -> Maybe String
  toString BadModel    _ = Nothing
  toString (Result xs) f = Just $ unlines (mkString xs)
    where
      mkString : List GoalNode -> List String
      mkString Nil     = Nil
      mkString (x::xs) = f x :: mkString xs
