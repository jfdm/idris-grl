||| Evaluation strategies for GRL instances.
|||
||| A evaluation strategies consists of the following three steps.
|||
||| 1. Initialize the evaluation values for the preselected strategy.
||| 2. Perform forward propagation of the evaluation values to other elements.
||| 3. Calculate the satisfaction of the actors.
|||
||| Once completed this module will provide the strategies described
||| in Amyot2010egm: Qualitative, Quantitative, and Hybrid. Currently
||| only the qualitative evaluation is provided.
|||
module GRL.Eval

import public Effects
import public Effect.State
import public Effect.Exception

import GRL.Types

EvalRes : Type
EvalRes = List (GModel ELEM, EvalVal)

EvalEffs : List EFFECT
EvalEffs = [STATE EvalRes]

instance [and] Ord EvalVal where
  compare SATISFIED SATISFIED = EQ
  compare WEAKSATIS WEAKSATIS = EQ
  compare WEAKDEN   WEAKDEN   = EQ
  compare DENIED    DENIED    = EQ
  compare CONFLICT  CONFLICT  = EQ
  compare UNKNOWN   UNKNOWN   = EQ
  compare NONE      NONE      = EQ
  compare UNDECIDED UNDECIDED = EQ
  compare DENIED    _         = LT
  compare _         DENIED    = GT
  compare CONFLICT  UNDECIDED = EQ
  compare UNDECIDED CONFLICT  = EQ
  compare CONFLICT  _         = LT
  compare _         CONFLICT  = GT
  compare UNDECIDED _         = LT
  compare _         UNDECIDED = GT
  compare WEAKDEN   _         = LT
  compare _         WEAKDEN   = GT
  compare NONE      _         = LT
  compare _         NONE      = GT
  compare WEAKSATIS _         = LT
  compare _         WEAKSATIS = GT
  compare SATISFIED _         = GT
  compare _         SATISFIED = LT

instance [or] Ord EvalVal where
  compare SATISFIED SATISFIED = EQ
  compare WEAKSATIS WEAKSATIS = EQ
  compare WEAKDEN   WEAKDEN   = EQ
  compare DENIED    DENIED    = EQ
  compare CONFLICT  CONFLICT  = EQ
  compare UNKNOWN   UNKNOWN   = EQ
  compare NONE      NONE      = EQ
  compare UNDECIDED UNDECIDED = EQ
  compare DENIED    _         = LT
  compare _         DENIED    = GT
  compare WEAKDEN   _         = LT
  compare _         WEAKDEN   = GT
  compare NONE      _         = LT
  compare _         NONE      = GT
  compare WEAKSATIS _         = LT
  compare _         WEAKSATIS = GT
  compare CONFLICT  UNDECIDED = EQ
  compare UNDECIDED CONFLICT  = EQ
  compare CONFLICT  _         = LT
  compare _         CONFLICT  = GT
  compare UNDECIDED _         = LT
  compare _         UNDECIDED = GT
  compare SATISFIED _         = GT
  compare _         SATISFIED = LT


-- fetchElems : GModel ELEM -> List (GModel ELEM)
-- fetchElems (Actor _ _ _ es _) = es ++ fetchElems es
-- fetchElems _                  = Nil

-- forwardProp : GLang MODEL -> {EvalEffs} Eff $ EvalRes
-- forwardProp (Spec es ls) = do
--    put $ es ++ fetchElems es
--    qualEval ls
