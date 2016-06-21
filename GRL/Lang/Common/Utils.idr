-- --------------------------------------------------------------- [ Utils.idr ]
-- Module    : Utils.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Lang.Common.Utils

import GRL.Common
import GRL.Model

%access export

prettyResult : GoalNode -> String
prettyResult g = unwords
    [ "Result:"
    , show (fromMaybe NONE (getSValue g))
    , "\t<=="
    , getNodeTitle g]

-- --------------------------------------------------------------------- [ EOF ]
