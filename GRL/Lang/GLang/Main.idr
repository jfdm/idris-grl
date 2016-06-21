-- ---------------------------------------------------------------- [ Main.idr ]
-- Module    : Main.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Serialiser and Parser and Evaluator for GLANG, quick and dirty.
module GRL.Lang.GLang.Main

import System

import Effects
import Effect.System
import Effect.StdIO
import Effect.State
import Effect.Exception
import Effect.File

import Data.AVL.Dict

import Lightyear
import Lightyear.Char
import Lightyear.Strings
import Lightyear.StringFile

import GRL.Lang.GLang

import GRL.Lang.GLang.Pretty
import GRL.Lang.Common.Error
import GRL.Lang.Common.Parser
import GRL.Lang.Common.Effs
import GRL.Lang.Common.Utils

import GRL.Eval


GLangE : Type -> Type
GLangE ty = Lang (GLang ELEM) ty

-- ------------------------------------------------------------------- [ Types ]

nodeTy : Parser GElemTy
nodeTy = (keyword "Goal" *> return GOALty)
     <|> (keyword "Soft" *> return SOFTty)
     <|> (keyword "Task" *> return TASKty)
     <|> (keyword "Res"  *> return RESty)
     <?> "Node Type"

intentTy : Parser GIntentTy
intentTy = (keyword "==>" *> return IMPACTSty)
       <|> (keyword "~~>" *> return AFFECTSty)
       <?> "Intent Type"

structTy : Parser GStructTy
structTy = (keyword "&=" *> return ANDty)
       <|> (keyword "|=" *> return IORty)
       <|> (keyword "X=" *> return XORty)
       <?> "Struct Type"

-- --------------------------------------------------------- [ Data Structures ]

node : Parser (GLangAST ELEM)
node = do
    n <- ident
    keyword "<-"
    ty <- nodeTy
    t <- quoted '"'
    sval <- opt $ keyword "is" *> sValue
    gComment
    pure (MkNode n ty t sval)
  <?> "Node"

intent : Parser (GLangAST INTENT)
intent = do
    x <- ident
    ty <- intentTy
    y <- ident
    keyword "|"
    cval <- cValue
    gComment
    pure (MkIntent ty cval x y)
  <?> "Intent"

struct : Parser (GLangAST STRUCT)
struct = do
    x <- ident
    ty <- structTy
    ys <- brackets $ commaSep1 ident
    gComment
    pure (MkStruct ty x ys)
  <?> "Struct"

-- ------------------------------------------------------- [ Model description ]

glang : Parser (ts ** DList GTy GLangAST ts)
glang = do
    gComment
    keyword "grl"
    keyword "model"
    gComment
    ns <- some node
    ss <- many struct
    is <- many intent

    let ns' = DList.fromList ns
    let ss' = DList.fromList ss
    let is' = DList.fromList is

    pure (_ ** (snd ns')
            ++ (snd ss')
            ++ (snd is'))
  <?> "GRL Model"

-- ----------------------------------------------------------- [ Strategy File ]

gstrategy : Parser $ List (String, SValue)
gstrategy = do
      gComment
      keyword "grl"
      keyword "strategy"
      gComment
      ss <- some pairing
      pure ss
    <?> "Strategy"
  where
    pairing : Parser (String, SValue)
    pairing = do
        i <- ident
        keyword "="
        sval <- sValue
        gComment
        pure (i,sval)

-- --------------------------------------------------------- [ Effectful Stuff ]

buildElem : GElemTy -> String -> GLangE (GLang ELEM)
buildElem GOALty t = pure $ mkGoal t
buildElem SOFTty t = pure $ mkSoft t
buildElem TASKty t = pure $ mkTask t
buildElem RESty  t = pure $ mkRes  t

buildElemSat : GElemTy -> String -> SValue -> GLangE (GLang ELEM)
buildElemSat GOALty t s = pure $ mkSatGoal t s
buildElemSat SOFTty t s = pure $ mkSatSoft t s
buildElemSat TASKty t s = pure $ mkSatTask t s
buildElemSat RESty  t s = pure $ mkSatRes  t s

insertE : GLangAST ty -> GModel -> GLangE GModel
insertE (MkNode i ty t Nothing) m = do
    g <- buildElem ty t
    update (\env => insert i g env)
    pure (insert g m)

insertE (MkNode i ty t (Just sval)) m = do
    g <- buildElemSat ty t sval
    update (\env => insert i g env)
    pure (insert g m)

insertE (MkIntent ty cval x y) m = do
    x' <- getElem x
    y' <- getElem y
    case ty of
      IMPACTSty => pure $ insert (x' ==> y' | cval) m
      AFFECTSty => pure $ insert (x' ~~> y' | cval) m

insertE (MkStruct ty x ys) m = do
    x' <- getElem x
    ys' <- mapE (\y => getElem y) ys
    case ty of
      ANDty => pure $ insert (x' &= ys') m
      XORty => pure $ insert (x' X= ys') m
      IORty => pure $ insert (x' |= ys') m

buildModel : DList GTy GLangAST ds -> GModel -> GLangE GModel
buildModel Nil     m = pure m
buildModel (d::ds) m = buildModel ds !(insertE d m)

buildStrategyE : List (String, SValue) -> GLangE Strategy
buildStrategyE is = do
    is' <- mapE (\x => doConv x) is
    pure $ buildStrategy is'
  where
    doConv : (String,SValue) -> GLangE (GLang ELEM, SValue)
    doConv (i,sval) = pure (!(getElem i), sval)

doEvaluateE : GModel
         -> Maybe String
         -> GLangE EvalResult
doEvaluateE m Nothing       = evaluateE m Nothing
doEvaluateE m (Just sfname) = do
    strat <- readLangFile gstrategy sfname
    strat' <- buildStrategyE strat
    evaluateE m (Just strat')

-- ------------------------------------------------------------------ [ Pretty ]

covering
eMain : GLangE ()
eMain = do
    as <- getArgs
    (mfname, sfname) <- processArgs as
    (_ ** ast) <- readLangFile glang mfname
    m <- buildModel ast emptyModel
    res <- doEvaluateE m sfname
    showRes prettyResult res
    putStrLn $ toString m

main : IO ()
main = do
  run eMain
  exit 0

-- --------------------------------------------------------------------- [ EOF ]
