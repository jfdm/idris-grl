-- -------------------------------------------------------------- [ Pretty.idr ]
-- Module    : Pretty.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Print pretty models.
module GRL.Pretty

import GRL.Model

||| Pretty models
prettyModel : GModel -> String
prettyModel g = (foldl (\res,x => show x ++ "\n" ++ res) "" (vertices g)) ++ "\n" ++
                (foldl (\res,x => show x ++ "\n" ++ res) "" (edges g))    ++ "\n"

-- --------------------------------------------------------------------- [ EOF ]
