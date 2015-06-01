||| The Internal Representation.
module DSL.IR

import GRL.Common

-- ---------------------------------------------------------- [ ADT Definition ]
data GrlIR : GrlIRTy -> Type where
  Element : (ty : GRLElementTy)
          -> String
          -> Maybe Satisfaction
          -> GrlIR ELEM

  IntentLink : (ty : GRLIntentTy)
           -> ContributionTy
           -> GrlIR ELEM
           -> GrlIR ELEM
           -> GrlIR INTENT

  StructureLink : (ty : Decomposition)
               -> GrlIR ELEM
               -> List (GrlIR ELEM)
               -> GrlIR STRUCT

partial
eqGrlIR : GrlIR a -> GrlIR b -> Bool
eqGrlIR (Element xty x sx) (Element yty y sy) =
    xty == yty && x == y && sx == sy
eqGrlIR (IntentLink xty xc xa xb) (IntentLink yty yc ya yb) =
    xty == yty && xc == yc && eqGrlIR xa ya && eqGrlIR xb yb
eqGrlIR (StructureLink xty xa (xbs)) (StructureLink yty ya (ybs)) =
      xty == yty && eqGrlIR xa ya && eqGrlIRList xbs ybs
    where
      eqGrlIRList : List (GrlIR ELEM) -> List (GrlIR ELEM) -> Bool
      eqGrlIRList Nil Nil = True
      eqGrlIRList Nil ys  = False
      eqGrlIRList (x::xs) (y::ys) = eqGrlIR x y && assert_smaller (eqGrlIRList xs ys) (eqGrlIRList xs ys)
eqGrlIR _ _ = False


class GRL (a : GrlIRTy -> Type) where
  mkGoal   : a ELEM   -> GrlIR ELEM
  mkIntent : a INTENT -> GrlIR INTENT
  mkStruct : a STRUCT -> GrlIR STRUCT

-- --------------------------------------------------------------------- [ EOF ]