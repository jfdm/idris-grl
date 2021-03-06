-- -------------------------------------------------------------- [ Common.idr ]
-- Module    : Common.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| Common enumerated types used.
module GRL.Common

import public Decidable.Equality

%default total
%access public export

data Importance = HIGH | MEDIUM | LOW | NO

-- data SValue = DENIED | WEAKDEN | WEAKSATIS | SATISFIED | CONFLICT | UNKNOWN | NONE | UNDECIDED
namespace Qualiative
  data SValue : Type where
    ||| The intentional element or indicator is sufficiently dissatisfied.
    DENIED : SValue
    ||| The intentional element is partially dissatisfied.
    WEAKDEN : SValue
    ||| The intentional element or indicator is partially satisfied.
    WEAKSATIS : SValue
    ||| The intentional element is sufficiently satisfied.
    SATISFIED : SValue
    ||| There are arguments strongly in favour and strongly against
    ||| the satisfaction of the intentional element.
    CONFLICT : SValue
    ||| The satisfaction level of the intentional element is unknown.
    UNDECIDED : SValue
    ||| The intentional element or indicator is neither satisfied nor dissatisfied.
    NONE : SValue

export
invertEval : SValue -> SValue
invertEval DENIED = SATISFIED
invertEval WEAKDEN = WEAKSATIS
invertEval WEAKSATIS = WEAKDEN
invertEval SATISFIED = DENIED
invertEval x         = x

--  data CValue = MAKES | HELPS | SOMEPOS | UNKNOWN | SOMENEG | BREAK | HURTS

namespace Contributions
  data CValue : Type where
    ||| The contribution is positive and sufficient.
    MAKES : CValue
    ||| The contribution is positive but not sufficient.
    HELPS : CValue
    ||| The contribution is positive, but the extent of the contribution is unknown.
    SOMEPOS : CValue
    ||| There is some contribution, but the extent and the degree (positive or negative) of the contribution is unknown.
    UNKNOWN : CValue
    ||| The contribution is negative, but the extent of the contribution is unknown.
    SOMENEG : CValue
    ||| The contribution of the contributing element is negative and sufficient.
    BREAK : CValue
    ||| The contribution is negative but not sufficient.
    HURTS : CValue

export
invertContrib : CValue -> CValue
invertContrib MAKES = HURTS
invertContrib HELPS = BREAK
invertContrib SOMEPOS = SOMENEG
invertContrib UNKNOWN = UNKNOWN
invertContrib SOMENEG = SOMEPOS
invertContrib BREAK = HELPS
invertContrib HURTS = MAKES

-- ------------------------------------------------------------------- [ Types ]

-- data GElemTy = GOALty | SOFTty | TASKty | RESty
-- data GIntentTy  = IMPACTty | AFFECTSty
-- data GStructTy  = ANDty | XORty | IORty | NOTty

data GTy = ELEM | INTENT | STRUCT

data GElemTy : Type where
    ||| A (hard) Goal is a condition or state of affairs in the
    ||| world that the stakeholders would like to achieve.
    |||
    ||| How the goal is to be achieved is not specified, allowing
    ||| alternatives to be considered. A goal can be either a business
    ||| goal or a system goal. A business goal expresses goals regarding
    ||| the business or state of the business affairs the individual or
    ||| organization wishes to achieve. A system goal expresses goals
    ||| the target system should achieve and generally describes the
    ||| functional requirements of the target information system.
    |||
    GOALty : GElemTy

    ||| Softgoals are often used to describe qualities and
    ||| non-functional aspects such as security, robustness,
    ||| performance, usability, etc.
    |||
    ||| A Softgoal is a condition or state of affairs in the world that
    ||| the actor would like to achieve, but unlike in the concept of
    ||| (hard) goal, there are no clear-cut criteria for whether the
    ||| condition is achieved, and it is up to subjective judgement and
    ||| interpretation of the modeller to judge whether a particular
    ||| state of affairs in fact achieves sufficiently the stated
    ||| softgoal.
    |||
    SOFTty : GElemTy

    ||| a Task specifies a particular way of doing something.
    |||
    ||| When a task is part of the decomposition of a (higher-level)
    ||| task, this restricts the higher-level task to that particular
    ||| course of action. Tasks can also be seen as the solutions in the
    ||| target system, which will address (or operationalize) goals and
    ||| softgoals. These solutions provide operations, processes, data
    ||| representations, structuring, constraints and agents in the
    ||| target system to meet the needs stated in the goals and
    ||| softgoals.
    |||
    TASKty : GElemTy

    ||| A Resource is a physical or informational entity, for which the
    ||| main concern is whether it is available.
    |||
    RESty : GElemTy

data GIntentTy : Type where
  ||| A Contribution defines the level of impact that the
  ||| satisfaction of a source intentional element or indicator has on
  ||| the satisfaction of a destination intentional element.
  IMPACTSty : GIntentTy
  |||  A correlation link emphasizes side-effects between intentional
  ||| elements in different categories or actor definitions.
  AFFECTSty : GIntentTy

data GStructTy : Type where
  ||| The AND Decomposition link enables the hierarchical
  ||| decomposition of a target intentional element by a source
  ||| element. A target intentional element can be decomposed into
  ||| many source intentional elements using as many decomposition
  ||| links. All of the source intentional elements are necessary for
  ||| the target intentional element to be satisfied.
  |||
  ANDty : GStructTy
  ||| The XOR Decomposition link enables the description of
  ||| alternative means of satisfying a target intentional element:
  ||| Mutually exclusive. The satisfaction of one and only one of the
  ||| sub-intentional elements is necessary to achieve the target.
  |||
  XORty : GStructTy
  ||| The IOR Decomposition link enables the description of
  ||| alternative means of satisfying a target intentional element:
  ||| Not mutually exclusive. The satisfaction of one of the
  ||| sub-intentional elements is sufficient to achieve the target,
  ||| but many sub-intentional elements can be satisfied.
  |||
  IORty : GStructTy

-- -------------------------------------------------------------------- [ Show ]

implementation Show GElemTy where
  show GOALty = "Goal"
  show SOFTty = "Soft"
  show TASKty = "Task"
  show RESty  = "Res"

implementation Show GIntentTy where
  show IMPACTSty = "CONTRIBUTION"
  show AFFECTSty = "CORRELATION"

implementation Show GStructTy where
  show ANDty  = "ANDTy"
  show XORty  = "XORTy"
  show IORty  = "IORTy"

implementation Show GTy where
  show ELEM   = "ELEM"
  show INTENT = "INTENT"
  show STRUCT = "STRUCT"

-- ---------------------------------------------------------------------- [ Eq ]

implementation Eq GElemTy where
  (==) GOALty GOALty = True
  (==) SOFTty SOFTty = True
  (==) TASKty TASKty = True
  (==) RESty  RESty  = True
  (==) _        _    = False

implementation Eq GIntentTy where
  (==) IMPACTSty IMPACTSty = True
  (==) AFFECTSty AFFECTSty = True
  (==) _         _         = False

implementation Eq GStructTy where
  (==) ANDty ANDty = True
  (==) XORty XORty = True
  (==) IORty IORty = True
  (==) _     _     = False

implementation Eq GTy where
  (==) ELEM   ELEM   = True
  (==) INTENT INTENT = True
  (==) STRUCT STRUCT = True
  (==) _      _      = False

-- --------------------------------------------------------------- [ Orderable ]
implementation Ord GTy where
  compare ELEM   ELEM   = EQ
  compare INTENT INTENT = EQ
  compare STRUCT STRUCT = EQ
  compare ELEM   _      = LT
  compare _      ELEM   = GT
  compare INTENT _      = LT
  compare _      INTENT = GT
  compare STRUCT _      = LT
  compare _      STRUCT = GT

-- -------------------------------------------------------------------- [ Show ]

implementation Show SValue where
  show SATISFIED = "SATISFIED"
  show WEAKSATIS = "WEAKSATIS"
  show WEAKDEN   = "WEAKDEN"
  show DENIED    = "DENIED"
  show CONFLICT  = "CONFLICT"
  show UNDECIDED = "UNDECIDED"
  show NONE      = "NONE"

implementation Eq SValue where
  (==) SATISFIED SATISFIED = True
  (==) WEAKSATIS WEAKSATIS = True
  (==) WEAKDEN   WEAKDEN   = True
  (==) DENIED    DENIED    = True
  (==) CONFLICT  CONFLICT  = True
  (==) UNDECIDED UNDECIDED = True
  (==) NONE      NONE      = True
  (==) _         _         = False

implementation Show CValue where
  show MAKES   = "MAKES"
  show HELPS   = "HELPS"
  show SOMEPOS = "SOMEPOS"
  show UNKNOWN = "UNKNOWN"
  show SOMENEG = "SOMENEG"
  show HURTS   = "HURTS"
  show BREAK   = "BREAKS"

implementation Eq CValue where
  (==) MAKES   MAKES   = True
  (==) HELPS   HELPS   = True
  (==) SOMEPOS SOMEPOS = True
  (==) UNKNOWN UNKNOWN = True
  (==) SOMENEG SOMENEG = True
  (==) HURTS   HURTS   = True
  (==) BREAK   BREAK   = True
  (==) _       _       = False

implementation Cast CValue String where
  cast MAKES   = "MAKES"
  cast HELPS   = "HELPS"
  cast SOMEPOS = "SOMEPOS"
  cast UNKNOWN = "UNKNOWN"
  cast SOMENEG = "SOMENEG"
  cast HURTS   = "HURTS"
  cast BREAK   = "BREAKS"


implementation Cast SValue String where
  cast SATISFIED = "SATISFIED"
  cast WEAKSATIS = "WEAKSATIS"
  cast WEAKDEN   = "WEAKDEN"
  cast DENIED    = "DENIED"
  cast CONFLICT  = "CONFLICT"
  cast UNDECIDED = "UNDECIDED"
  cast NONE      = "NONE"

implementation Cast String CValue where
  cast "MAKES"   = MAKES
  cast "HELPS"   = HELPS
  cast "SOMEPOS" = SOMEPOS
  cast "UNKNOWN" = UNKNOWN
  cast "SOMENEG" = SOMENEG
  cast "HURTS"   = HURTS
  cast "BREAKS"  = BREAK
  cast _         = UNKNOWN

implementation Cast String SValue where
  cast "SATISFIED"   = SATISFIED
  cast "WEAKSATIS"   = WEAKSATIS
  cast "WEAKDEN"     = WEAKDEN
  cast "DENIED"      = DENIED
  cast "CONFLICT"    = CONFLICT
  cast "UNDECIDED"   = UNDECIDED
  cast "NONE"        = NONE
  cast _             = NONE

-- --------------------------------------------------------------------- [ EOF ]
