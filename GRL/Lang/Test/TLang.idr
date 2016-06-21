-- ------------------------------------------------------------- [ Example.idr ]
-- Module    : Example.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Lang.Test.TLang

import GRL.Lang.TLang

-- ------------------------------------------------------------ [ Sample Model ]
gpcePaper : TASK
gpcePaper = MkTask "Write GPCE paper"

gpceAbstract : SUBTASK
gpceAbstract = MkSTask "Write the abstract"

writePaper : SUBTASK
writePaper = MkSTask "Write the paper"

doWriting : ACTION
doWriting = MkAction "Do writing"

paperPlan : GModel
paperPlan = emptyModel
  \= gpcePaper
  \= gpceAbstract
  \= writePaper
  \= doWriting
  \= (gpcePaper &= gpceAbstract)
  \= (gpcePaper &= writePaper)
  \= (doWriting ==> writePaper   | MAKES)
  \= (doWriting ==> gpceAbstract | MAKES)

-- -------------------------------------------------------------------- [ Test ]
export
runTest : IO ()
runTest = do
    putStrLn $ prettyModel paperPlan
-- --------------------------------------------------------------------- [ EOF ]
