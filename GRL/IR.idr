-- ------------------------------------------------------------------ [ IR.idr ]
-- Module    : IR.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

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

-- -------------------------------------------------------------------- [ Show ]

private
shGExprE : GExpr ELEM -> String
shGExprE (Elem ty t ms) = with List unwords ["[Element", show ty, show t, show ms,"]"]

private
shGExprI : GExpr INTENT -> String
shGExprI (ILink ty cty a b) = with List unwords ["[Intent", show ty, show cty, shGExprE a, shGExprE b, "]"]

private
shGExprS : GExpr STRUCT -> String
shGExprS (SLink ty x ys) = with List unwords ["[Structure", show ty, shGExprE x, show' ys, "]"]
  where
    show' : List (GExpr ELEM) -> String
    show' ys = "[" ++ (unwords $ intersperse "," (map shGExprE ys)) ++ "]"

shGExpr : {ty : GTy} -> GExpr ty -> String
shGExpr {ty=ELEM}   x = shGExprE x
shGExpr {ty=INTENT} x = shGExprI x
shGExpr {ty=STRUCT} x = shGExprS x

instance Show (GExpr ty) where
  show x = shGExpr x

-- ------------------------------------------------------------- [ Eq Instance ]

private
eqGExprE : GExpr ELEM -> GExpr ELEM -> Bool
eqGExprE (Elem xty x sx) (Elem yty y sy) = xty == yty && x == y && sx == sy

private
eqGExprI : GExpr INTENT -> GExpr INTENT -> Bool
eqGExprI (ILink xty xc xa xb) (ILink yty yc ya yb) = xty == yty && xc == yc && eqGExprE xa ya && eqGExprE xb yb

private
eqGExprS : GExpr STRUCT -> GExpr STRUCT -> Bool
eqGExprS (SLink xty xa (xbs)) (SLink yty ya (ybs)) =
      xty == yty && eqGExprE xa ya && eqGExprList xbs ybs
    where
      eqGExprList : List (GExpr ELEM) -> List (GExpr ELEM) -> Bool
      eqGExprList Nil Nil = True
      eqGExprList (x::xs) (y::ys) =
        if eqGExprE x y
          then (eqGExprList (assert_smaller (x::xs) xs) (assert_smaller (y::ys) ys))
          else False
      eqGExprList _       _       = False

eqGExpr : GExpr a -> GExpr b -> Bool
eqGExpr {a=ELEM}   {b=ELEM}   x y = eqGExprE x y
eqGExpr {a=INTENT} {b=INTENT} x y = eqGExprI x y
eqGExpr {a=STRUCT} {b=STRUCT} x y = eqGExprS x y
eqGExpr _          _          = False

instance Eq (GExpr ty) where
  (==) x y = eqGExpr x y

||| The GRL Class for allowing DSL designers to instruct the Goal
||| Graph builder how to convert expressions in the DSL to the IR.
|||
||| @a The DSL which is indexed by `GTy` type.
class GRL (a : GTy -> Type) where
  ||| Instruct the interpreter to construct a goal node.
  mkElem   : a ELEM   -> GExpr ELEM
  ||| Intruct the interpreter to construct a intent link.
  mkIntent : a INTENT -> GExpr INTENT
  ||| Instruct the interpreter to consturct a structural link.
  mkStruct : a STRUCT -> GExpr STRUCT

-- --------------------------------------------------------------------- [ EOF ]
