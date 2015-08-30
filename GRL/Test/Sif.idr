module GRL.Test.Sif

import GRL.Lang.GLang
import GRL.Eval

import GRL.Test.Utils

%default total
%access public

g1 : GOAL
g1 = mkGoal "[Goal Requirement: Suitable Security Level Nothing ]"

g2 : TASK
g2 = mkGoal "[Goal Requirement: Data Confidentiality Nothing ]"

g3 : TASK
g3 = mkTask "[Goal Requirement: Recipient Confidentiality Nothing ]"

g4 : TASK
g4 = mkTask "[Goal Requirement: Suitable performance Nothing ]"

g5 : TASK
g5 = mkTask "[Goal Requirement: Minimal Workflow Disruption Nothing ]"

g6 : TASK
g6 = mkTask "[Goal Requirement: Secure Implementation Nothing ]"

g7 : TASK
g7 = mkTask "[Goal Requirement: Comprehensible by Non-Experts Nothing ]"

model : GModel
model = insertMany [g1,g2,g3,g4,g5,g6,g7] emptyModel

t1 : TASK
t1 = mkTask "Task Solution: Public Key Cryptography Nothing"

t2 : TASK
t2 = mkTask "[Task Property: Maths Algorithm Nothing ]"

t3 : TASK
t3 = mkTask "[Task Property: Implementation in Code Nothing ]"

t4 : TASK
t4 = mkTask "[Task Property: Key Pairs Nothing ]"

t5 : TASK
t5 = mkTask "[Task Property: Variable Security Parameters Nothing ]"

t6 : TASK
t6 = mkSatTask "t6" SATISFIED

t7 : TASK
t7 = mkSatTask "[Task Trait Disadvantage: Computationally Expensive Just WEAKDEN ]" WEAKDEN

t12 : TASK
t12 = mkSatTask "[Task Trait Disadvantage: Implementation InSecure Just WEAKDEN ]" WEAKDEN

t13 : TASK
t13 = mkSatTask "[Task Trait Disadvantage: Implementation obfuscates understanding Just WEAKSATIS ]" WEAKSATIS

t16 : TASK
t16 = mkSatTask "[Task Trait Advantage: PublicEnc/PrivateDec Keys Just SATISFIED ]" SATISFIED

t17 : TASK
t17 = mkSatTask "[Task Trait Disadvantage: Key Distribution Just DENIED ]" DENIED

t18 : TASK
t18 = mkSatTask "[Task Trait Disadvantage: Key Management Just DENIED ]" DENIED

t19 : TASK
t19 = mkSatTask "[Task Trait Advantage: Greater Security Just SATISFIED ]" SATISFIED

t20 : TASK
t20 = mkSatTask "[Task Trait Disadvantage: Parameter Selection Just DENIED ]" DENIED

t21 : TASK
t21 = mkSatTask "[Task Trait Disadvantage: Parameter Computation Just DENIED ]" DENIED


decls : (ds ** DList GTy GLang ds)
decls = (_ **
   [ t1,
     mkAnd t1 [ t2, t3 , t4 , t5],
     t2 , t6 , t7 ,
     mkImpacts HELPS t6 g2 ,
     mkImpacts HELPS t6 g3 ,
     mkImpacts HURTS t7 g4 ,
     mkImpacts HURTS t7 g5 ,
     mkAnd t2 [t6 , t7],
     t3 , t12 , t13 ,
     mkImpacts SOMENEG t12 g3 ,
     mkImpacts SOMENEG t12 g2 ,
     mkImpacts UNKNOWN t12 g5 ,
     mkImpacts SOMENEG t12 g6 ,
     mkImpacts HURTS t13 g7 ,
     mkImpacts HURTS t13 g5 ,
     mkAnd t3 [t12 , t13],
     t4 , t16 , t17 , t18 ,
     mkImpacts MAKES t16 g3 ,
     mkImpacts SOMENEG t17 g3 ,
     mkImpacts SOMENEG t17 g5 ,
     mkImpacts SOMENEG t18 g2 ,
     mkAnd t4 [t16 , t17 , t18] ,
     t5 , t19 , t20 , t21 ,
     mkImpacts HELPS t19 g1 ,
     mkImpacts SOMENEG t20 g1 ,
     mkImpacts SOMENEG t20 g6 ,
     mkImpacts HURTS t21 g4 ,
     mkImpacts HURTS t21 g5 ,
     mkAnd t5 [t19 , t20 , t21]
     ])

partial
runTest : IO ()
runTest = do
  let (_ ** ds) = groupDecls (getProof decls)
  putStrLn "Strategy 1:"
  let m = (insertMany' ds model)
  runEval m Nothing
