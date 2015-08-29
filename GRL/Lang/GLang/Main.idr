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
import Lightyear.Strings

import GRL.Lang.GLang
import GRL.Eval

-- -------------------------------------------------------------- [ Directives ]

%default partial
%access public

-- ----------------------------------------------------------------- [ Helpers ]

||| The 'context' environment
GEnv : Type
GEnv = Dict String (GLang ELEM)

instance Default GEnv where
  default = empty


-- ------------------------------------------------------------------ [ Errors ]

data GError : Type where
  NoFileError      : GError
  NoSuchFileError  : String -> GError
  ParserError      : String -> String -> GError
  NoSuchIdentError : String -> GError
  BadModelError    : GError

instance Show GError where
  show (NoFileError)            = "File Must Be specified"
  show (NoSuchFileError fn)     = unwords ["No such file:", show fn]
  show (ParserError fn err)     = unlines [unwords ["Unable to parse", show fn, "because:"], err]
  show (NoSuchIdentError ident) = unwords ["No such identifier:", show ident]
  show (BadModelError)          = "Bad Model"

-- ------------------------------------------------------------ [ Parser Utils ]
manyTill : Monad m => ParserT m String a
                   -> ParserT m String b
                   -> ParserT m String (List a)
manyTill p end = scan
  where
    scan : Monad m => ParserT m String (List a)
    scan = do { end; return List.Nil } <|>
           do { x <- p; xs <- scan; return (x::xs)}

eol : Parser Char
eol = char '\n'

anyChar : Parser Char
anyChar = satisfy (const True)

literalLR : Char -> Char -> Parser String
literalLR l r =
    map pack $ between (lexeme $ char l) (lexeme $ char r) (some (satisfy (/= r)))

literal : Char -> Parser String
literal c = literalLR c c

-- ------------------------------------------------------ [ Parsing Lang Utils ]

comment : String -> String -> String -> Parser ()
comment l b e = (line l    *> pure ())
            <|> (block b e *> pure ())
            <|> space
            <?> "Comment"
    where
      line : String -> Parser String
      line l = do
          token l
          doc <- manyTill anyChar eol
          space
          pure $ pack doc
        <?> "Line comment"

      block : String -> String -> Parser String
      block b e = do
          token b
          doc <- manyTill anyChar (token e)
          space
          pure $ pack doc
        <?> "Block Comment"

keyword : String -> Parser ()
keyword s = do
    string s
    space
    pure ()
  <?> "Keywords"

ident : Parser String
ident = lexeme (map pack $ some identChar) <?> "Identity"
  where
    identChar : Parser Char
    identChar = (satisfy isAlphaNum) <?> "Ident Char"

quoted : Parser String
quoted = literal '"' <?> "Quoted String"
-- ------------------------------------------------------------ [ GLang Parser ]

gComment : Parser ()
gComment = comment "--" "{-" "-}" <?> "Comment"

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

cValue : Parser CValue
cValue = (keyword "Makes"   *> return MAKES)
     <|> (keyword "Helps"   *> return HELPS)
     <|> (keyword "SomePos" *> return SOMEPOS)
     <|> (keyword "Unknown" *> return UNKNOWN)
     <|> (keyword "SomeNeg" *> return SOMENEG)
     <|> (keyword "Breaks"  *> return BREAK)
     <|> (keyword "Hurts"   *> return HURTS)
     <?> "CValue"

sValue : Parser SValue
sValue = (keyword "Denied"    *> return DENIED)
     <|> (keyword "WeakDen"   *> return WEAKDEN)
     <|> (keyword "WeakSatis" *> return WEAKSATIS)
     <|> (keyword "Satisfied" *> return SATISFIED)
     <|> (keyword "Undecided" *> return UNDECIDED)
     <|> (keyword "None"      *> return NONE)
     <?> "Trait Type"


node : Parser (GLangAST ELEM)
node = do
    n <- ident
    keyword "<-"
    ty <- nodeTy
    t <- quoted
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

    pure (_ ** (getProof ns')
            ++ (getProof ss')
            ++ (getProof is'))
  <?> "GRL Model"

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

GEffs : List EFFECT
GEffs = [SYSTEM, FILE_IO (), STDIO, STATE GEnv, EXCEPTION GError]


readGRLFile : Parser a
           -> String
           -> Eff a GEffs
readGRLFile p f = do
    case !(open f Read) of
      True => do
        src <- readAcc ""
        close
        case parse p src of
          Left err  => raise (ParserError f err)
          Right res => pure res
      False => raise (NoSuchFileError f)
  where
    readAcc : String -> Eff String [FILE_IO (OpenFile Read)]
    readAcc acc = if (not !(eof))
                     then readAcc (acc ++ !(readLine))
                     else pure acc


buildElem : GElemTy -> String -> Eff (GLang ELEM) GEffs
buildElem GOALty t = pure $ mkGoal t
buildElem SOFTty t = pure $ mkSoft t
buildElem TASKty t = pure $ mkTask t
buildElem RESty  t = pure $ mkRes  t

buildElemSat : GElemTy -> String -> SValue -> Eff (GLang ELEM) GEffs
buildElemSat GOALty t s = pure $ mkSatGoal t s
buildElemSat SOFTty t s = pure $ mkSatSoft t s
buildElemSat TASKty t s = pure $ mkSatTask t s
buildElemSat RESty  t s = pure $ mkSatRes  t s

fetchElem : String -> Eff (GLang ELEM) GEffs
fetchElem id = do
  env <- get
  case (lookup id env) of
    Nothing => raise $ NoSuchIdentError id
    Just e  => pure e

insertE : GLangAST ty -> GModel -> Eff GModel GEffs
insertE (MkNode i ty t Nothing) m = do
    g <- buildElem ty t
    update (\env => insert i g env)
    pure (insert g m)

insertE (MkNode i ty t (Just sval)) m = do
    g <- buildElemSat ty t sval
    update (\env => insert i g env)
    pure (insert g m)

insertE (MkIntent ty cval x y) m = do
    x' <- fetchElem x
    y' <- fetchElem y
    case ty of
      IMPACTSty => pure $ insert (x' ==> y' | cval) m
      AFFECTSty => pure $ insert (x' ~~> y' | cval) m

insertE (MkStruct ty x ys) m = do
    x' <- fetchElem x
    ys' <- mapE (\y => fetchElem y) ys
    case ty of
      ANDty => pure $ insert (x' &= ys') m
      XORty => pure $ insert (x' X= ys') m
      IORty => pure $ insert (x' |= ys') m

buildModel : DList GTy GLangAST ds -> GModel -> Eff GModel GEffs
buildModel Nil     m = pure m
buildModel (d::ds) m = buildModel ds !(insertE d m)

buildStrategyE : List (String, SValue) -> Eff Strategy GEffs
buildStrategyE is = do
    is' <- mapE (\x => doConv x) is
    pure $ buildStrategy is'
  where
    doConv : (String,SValue) -> Eff (GLang ELEM, SValue) GEffs
    doConv (i,sval) = pure (!(fetchElem i), sval)

covering
processArgs : List String -> Eff (String, Maybe String) GEffs
processArgs Nil           = raise NoFileError
processArgs [x]           = raise NoFileError
processArgs [x,y]         = pure (y, Nothing)
processArgs (x::y::z::xs) = pure (y, Just z)

prettyResult : GoalNode -> String
prettyResult g = unwords
    [ "Result:"
    , show (fromMaybe NONE (getSValue g))
    , "\t<=="
    , getNodeTitle g]

evalModelE : GModel -> Maybe String -> Eff EvalResult GEffs
evalModelE m Nothing       = pure $ evalModel m Nothing
evalModelE m (Just sfname) = do
    strat <- readGRLFile gstrategy sfname
    strat' <- buildStrategyE strat
    pure $ evalModel m (Just strat')

-- ------------------------------------------------------------------ [ Pretty ]


showRes : EvalResult -> Eff () GEffs
showRes res =
    case toString res prettyResult of
      Nothing  => raise BadModelError
      Just res => putStrLn res

covering
eMain : Eff () GEffs
eMain = do
    as <- getArgs
    (mfname, sfname) <- processArgs as
    (_ ** ast) <- readGRLFile glang mfname
    m <- buildModel ast emptyModel
    res <- evalModelE m sfname
    showRes res
    putStrLn $ toString m

main : IO ()
main = do
  run eMain
  exit 0

-- --------------------------------------------------------------------- [ EOF ]
