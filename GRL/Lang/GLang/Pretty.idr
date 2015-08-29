-- -------------------------------------------------------------- [ Pretty.idr ]
-- Module    : Pretty.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module GRL.Lang.GLang.Pretty

import public GRL.Common
import public GRL.IR
import public GRL.Model

%access public
%default total

data GLangAST : GTy -> Type where
    MkNode   : String -> GElemTy -> String -> Maybe SValue -> GLangAST ELEM
    MkIntent : GIntentTy -> CValue -> String -> String -> GLangAST INTENT
    MkStruct : GStructTy -> String -> List (String) -> GLangAST STRUCT

showSValue : Maybe SValue -> String
showSValue Nothing     = ""
showSValue (Just sval) = unwords ["is", show sval]

listIDs : List String -> String
listIDs is = unwords $ intersperse "," is

showIntent : String -> CValue -> String -> String -> String
showIntent op cval x y = unwords [x, op, y, "|", show cval]

showStruct : String -> String -> List String -> String
showStruct op x ys = unwords [x, op, "[", listIDs ys, "]" ]

instance Show (GLangAST ty) where
  show (MkNode id ty t sval) = unwords [id, "<-", show ty, show t, showSValue sval]
  show (MkIntent ty cval x y) =
      case ty of
        IMPACTSty => showIntent "==>" cval x y
        AFFECTSty => showIntent "~~>" cval x y
  show (MkStruct ty x ys) =
      case ty of
        ANDty => showStruct "&=" x ys
        XORty => showStruct "X=" x ys
        IORty => showStruct "|=" x ys

-- ----------------------------------------------------------- [ The FUnctions ]

private
mkPrefix : GElemTy -> String
mkPrefix GOALty = "g"
mkPrefix SOFTty = "s"
mkPrefix TASKty = "t"
mkPrefix RESty  = "r"

private
mkStructOp : GStructTy -> String
mkStructOp ANDty = "&="
mkStructOp XORty = "X="
mkStructOp IORty = "|="

private
prettyElem : NodeID -> GoalNode -> String
prettyElem id n = with List show (MkNode
    (concat [mkPrefix (getNodeTy n), show id])
    (getNodeTy n)
    (getNodeTitle n)
    (getSValue n))

private
genIDs : List (GoalNode, NodeID) -> Dict NodeID String
genIDs is = foldl doInsert empty is
  where
    doInsert : Dict NodeID String -> (GoalNode, NodeID) -> Dict NodeID String
    doInsert dict (g,id) = with List
        insert id (concat [mkPrefix (getNodeTy g), show id]) dict

private
fetchID : NodeID -> Dict NodeID String -> String
fetchID n dict =
    case lookup n dict of
      Nothing  => "No ID this will fail"
      Just val => val

private
prettyStruct : String -> GStructTy -> List String -> String
prettyStruct x ty ys = show $ MkStruct ty x ys

private
prettyStructs : NodeID -> Dict NodeID String -> GModel -> Maybe String
prettyStructs n dict m =
    case getValueByID n m of
      Nothing   => Nothing
      Just nVal =>
        case getStructTy nVal of
          Nothing => Nothing
          Just s  => Just $ prettyStruct (fetchID n dict) s ys'

  where
    ys : List NodeID
    ys = map fst $ filter (\(y,l) => isDeCompEdge l) (getEdgesByID n m)

    ys' : List String
    ys' = map (\x => fetchID x dict) ys

private
prettyIntents : NodeID -> Dict NodeID String -> GModel -> String
prettyIntents n dict m = unlines $ map prettyIntent ys'
  where
    x : String
    x = fetchID n dict

    ys' : List (DemiEdge GoalEdge)
    ys' = filter (\(y,l) => not $ isDeCompEdge l) (getEdgesByID n m)

    prettyIntent : DemiEdge GoalEdge -> String
    prettyIntent (yID, Just (Correlation cval))  =
        show $ MkIntent AFFECTSty cval (fetchID yID dict) x
    prettyIntent (yID, Just (Contribution cval)) =
        show $ MkIntent IMPACTSty cval (fetchID yID dict) x
    prettyIntent _  = "-- err"


namespace GLang
  toString : GModel -> String
  toString m = unlines
      [ "grl model\n"
      , unlines es, "\n"
      , unlines (catMaybes ss), "\n"
      , unlines is, "\n"
      , "\n"
      ]
    where
      ids : Dict NodeID String
      ids = genIDs (legend m)

      es : List String
      es = foldr (\(k,v),res => prettyElem v k :: res) Nil (legend m)

      is : List String
      is = map (\n => prettyIntents n ids m) (verticesID m)

      ss : List (Maybe String)
      ss = map (\n => prettyStructs n ids m) (verticesID m)


-- --------------------------------------------------------------------- [ EOF ]
