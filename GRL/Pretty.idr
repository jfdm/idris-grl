module GRL.Pretty

import GRL.Model

-- ppRes : Show a => List (a) -> IO ()
-- ppRes Nil     = printLn ""
-- ppRes (x::xs) = do
--   printLn x
--   ppRes xs

prettyModel : GModel -> String
prettyModel g = (foldl (\res,x => show x ++ "\n" ++ res) "" (vertices g)) ++ "\n" ++
                (foldl (\res,x => show x ++ "\n" ++ res) "" (edges g))    ++ "\n"
