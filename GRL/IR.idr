||| The intermediate representation for GRL-Derived Languages.
module DSL.IR

import GRL.Common

%access public
-- ---------------------------------------------------------- [ AST Definition ]

||| An IR to aid in converting DSL language constructs into Goal Graph
||| objects.
data GExpr : GTy -> Type where
  Elem  : GElemTy -> String -> Maybe SValue -> GExpr ELEM
  ILink : GIntentTy -> CValue -> GExpr ELEM -> GExpr ELEM -> GExpr INTENT
  SLink : GStructTy -> GExpr ELEM -> List (GExpr ELEM) -> GExpr STRUCT


getTitle : GExpr ELEM -> String
getTitle (Elem ty t s) = t

instance Show (GExpr ty) where
  show (Elem ty t ms) = with List unwords ["[Element", show ty, show t, show ms,"]"]
  show (ILink ty cty a b) = with List unwords ["[Intent", show ty, show cty, show a, show b, "]"]
  show (SLink ty x ys) = with List unwords ["[Structure", show ty, show x, show ys, "]"]

partial
eqGExpr : GExpr a -> GExpr b -> Bool
eqGExpr (Elem xty x sx) (Elem yty y sy) =
    xty == yty && x == y && sx == sy
eqGExpr (ILink xty xc xa xb) (ILink yty yc ya yb) =
    xty == yty && xc == yc && eqGExpr xa ya && eqGExpr xb yb
eqGExpr (SLink xty xa (xbs)) (SLink yty ya (ybs)) =
      xty == yty && eqGExpr xa ya && eqGExprList xbs ybs
    where
      eqGExprList : List (GExpr ELEM) -> List (GExpr ELEM) -> Bool
      eqGExprList Nil Nil = True
      eqGExprList Nil ys  = False
      eqGExprList (x::xs) (y::ys) = eqGExpr x y && assert_smaller (eqGExprList xs ys) (eqGExprList xs ys)
eqGExpr _ _ = False


||| The GRL Class for allowing DSL designers to instruct the Goal
||| Graph builder how to convert expressions in the DSL to the IR.
|||
||| @a The DSL which is indexed by `GTy` type.
class GRL (a : GTy -> Type) where
  mkGoal   : a ELEM   -> GExpr ELEM
  mkIntent : a INTENT -> GExpr INTENT
  mkStruct : a STRUCT -> GExpr STRUCT

-- --------------------------------------------------------------------- [ EOF ]
