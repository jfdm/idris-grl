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
import public Effect.StdIO

import public GRL.Eval.Qualitative
import public GRL.Eval.Forward
import public GRL.Eval.Strategy
import public GRL.Eval.Common
