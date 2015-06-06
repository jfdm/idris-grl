||| The original unabulterated version of the GRL.
module GRL.Lang.Default

import public GRL.Common
import public GRL.IR
import public GRL.Model
import public GRL.Builder

%access public

||| The original unabulterated version of the GRL.
data GoalLang : GrlIRTy -> Type where
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
    MkGoal : String -> Maybe Satisfaction -> GoalLang ELEM

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
    MkSoft : String -> Maybe Satisfaction -> GoalLang ELEM

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
    MkTask : String -> Maybe Satisfaction -> GoalLang ELEM

    ||| A Resource is a physical or informational entity, for which the
    ||| main concern is whether it is available.
    |||
    MkResource : String -> Maybe Satisfaction -> GoalLang ELEM

    ||| A Contribution defines the level of impact that the
    ||| satisfaction of a source intentional element or indicator has on
    ||| the satisfaction of a destination intentional element.
    MkImpacts : ContributionTy
             -> GoalLang ELEM
             -> GoalLang ELEM
             -> GoalLang INTENT

    |||  A correlation link emphasizes side-effects between intentional
    ||| elements in different categories or actor definitions.
    MkEffects : ContributionTy
            -> GoalLang ELEM
            -> GoalLang ELEM
            -> GoalLang INTENT

    ||| The AND Decomposition link enables the hierarchical
    ||| decomposition of a target intentional element by a source
    ||| element. A target intentional element can be decomposed into
    ||| many source intentional elements using as many decomposition
    ||| links. All of the source intentional elements are necessary for
    ||| the target intentional element to be satisfied.
    |||
    MkAnd : GoalLang ELEM
          -> List (GoalLang ELEM)
          -> GoalLang STRUCT

    ||| The XOR Decomposition link enables the description of
    ||| alternative means of satisfying a target intentional element:
    ||| Mutually exclusive. The satisfaction of one and only one of the
    ||| sub-intentional elements is necessary to achieve the target.
    |||
    MkXor : GoalLang ELEM
         -> List (GoalLang ELEM)
         -> GoalLang STRUCT

    ||| The IOR Decomposition link enables the description of
    ||| alternative means of satisfying a target intentional element:
    ||| Not mutually exclusive. The satisfaction of one of the
    ||| sub-intentional elements is sufficient to achieve the target,
    ||| but many sub-intentional elements can be satisfied.
    |||
    MkIor : GoalLang ELEM
         -> List (GoalLang ELEM)
         -> GoalLang STRUCT


GOAL : Type
GOAL = GoalLang ELEM

SOFT : Type
SOFT = GoalLang ELEM

TASK : Type
TASK = GoalLang ELEM

RES : Type
RES = GoalLang ELEM


syntax [a] "==>" [b] "|" [c] = MkImpacts c a b
syntax [a] "~~>" [b] "|" [c] = MkEffects c a b
syntax [a] "&=" [b] = MkAnd a b
syntax [a] "X=" [b] = MkXor a b
syntax [a] "|=" [b] = MkIor a b


instance GRL GoalLang where
    mkGoal (MkGoal     s e) = Element GOALTy s e
    mkGoal (MkSoft     s e) = Element SOFTTy s e
    mkGoal (MkTask     s e) = Element TASKTy s e
    mkGoal (MkResource s e) = Element RESOURCETy s e

    mkIntent (MkImpacts c a b) = IntentLink CONTRIBUTION c (mkGoal a) (mkGoal b)
    mkIntent (MkEffects c a b) = IntentLink CORRELATION  c (mkGoal a) (mkGoal b)

    mkStruct (MkAnd a bs) = StructureLink ANDTy (mkGoal a) (map (mkGoal) bs)
    mkStruct (MkXor a bs) = StructureLink XORTy (mkGoal a) (map (mkGoal) bs)
    mkStruct (MkIor a bs) = StructureLink IORTy (mkGoal a) (map (mkGoal) bs)

-- --------------------------------------------------------------------- [ EOF ]
