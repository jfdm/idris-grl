module GRL.DSL

import GRL.Types.Expr
import GRL.Types.Value

-- ---------------------------------------------------------- [ ADT Definition ]
data GRLExpr : GRLExprTy -> Type where
  Element : (ty : GRLElementTy)
          -> String
          -> Maybe Satisfaction
          -> GRLExpr ELEM

  IntentLink : (ty : GRLIntentTy)
           -> ContributionTy
           -> GRLExpr ELEM
           -> GRLExpr ELEM
           -> GRLExpr INTENT

  StructureLink : (ty : GRLStructTy)
               -> GRLExpr ELEM
               -> GRLExpr ELEM
               -> GRLExpr STRUCT

-- ---------------------------------------------------- [ Element Declarations ]
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
goal : String -> Maybe Satisfaction -> GRLExpr ELEM
goal s e = Element GOAL s e

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
soft : String -> Maybe Satisfaction -> GRLExpr ELEM
soft s e = Element SOFT s e

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
task : String -> Maybe Satisfaction -> GRLExpr ELEM
task s e = Element TASK s e

||| A Resource is a physical or informational entity, for which the
||| main concern is whether it is available.
|||
resource : String -> Maybe Satisfaction -> GRLExpr ELEM
resource s e = Element RESOURCE s e

-- ------------------------------------------------ [ Intentional Declarations ]
||| A Contribution defines the level of impact that the
||| satisfaction of a source intentional element or indicator has on
||| the satisfaction of a destination intentional element.
impacts : ContributionTy
        -> GRLExpr ELEM
        -> GRLExpr ELEM
        -> GRLExpr INTENT
impacts c a b = IntentLink CONTRIBUTION c a b

|||  A correlation link emphasizes side-effects between intentional
||| elements in different categories or actor definitions.
effects : ContributionTy
        -> GRLExpr ELEM
        -> GRLExpr ELEM
        -> GRLExpr INTENT
effects c a b = IntentLink CORRELATION c a b

-- ------------------------------------------------- [ Structural Declarations ]
||| The AND Decomposition link enables the hierarchical
||| decomposition of a target intentional element by a source
||| element. A target intentional element can be decomposed into
||| many source intentional elements using as many decomposition
||| links. All of the source intentional elements are necessary for
||| the target intentional element to be satisfied.
|||
and : GRLExpr ELEM
   -> GRLExpr ELEM
   -> GRLExpr STRUCT
and a bs = StructureLink AND a bs

||| The XOR Decomposition link enables the description of
||| alternative means of satisfying a target intentional element:
||| Mutually exclusive. The satisfaction of one and only one of the
||| sub-intentional elements is necessary to achieve the target.
|||
xor : GRLExpr ELEM
   -> GRLExpr ELEM
   -> GRLExpr STRUCT
xor a bs = StructureLink XOR a bs

||| The IOR Decomposition link enables the description of
||| alternative means of satisfying a target intentional element:
||| Not mutually exclusive. The satisfaction of one of the
||| sub-intentional elements is sufficient to achieve the target,
||| but many sub-intentional elements can be satisfied.
|||
ior : GRLExpr ELEM
   -> GRLExpr ELEM
   -> GRLExpr STRUCT
ior a bs = StructureLink IOR a bs


-- --------------------------------------------------------------------- [ EOF ]
