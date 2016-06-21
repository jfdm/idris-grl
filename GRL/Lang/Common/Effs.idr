-- ---------------------------------------------------------------- [ Effs.idr ]
-- Module    : Effs.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Effectful definitions
module GRL.Lang.Common.Effs

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

import GRL.Common
import GRL.Model
import GRL.IR
import GRL.Builder

import GRL.Lang.Common.Error

import GRL.Eval

%access export

-- ----------------------------------------------------------------- [ Context ]

public export
GEnv : Type -> Type
GEnv val = Dict String val

Default (GEnv a) where
  default = empty

-- ------------------------------------------------------- [ Effectful Context ]
public export
Lang : Type -> Type -> Type
Lang cTy rTy = Eff rTy
                   [ SYSTEM
                   , FILE_IO ()
                   , STDIO
                   , STATE (GEnv cTy)
                   , EXCEPTION GError]


||| Read in a language specification
readLangFile : Parser a
            -> String
            -> Lang ty a
readLangFile p f = do
    res <- parseFile (NoSuchFileError) (ParserError) p f
    case res of
      Left err  => raise err
      Right ast => pure ast

||| Add element to the context.
getElem : String -> Lang cTy cTy
getElem id = do
  env <- get
  case (lookup id env) of
    Nothing => raise $ NoSuchIdentError id
    Just e  => pure e

evaluateE : GModel
         -> Maybe Strategy
         -> Lang cTy EvalResult
evaluateE m strat = pure $ evaluate FORWARD strat m


processArgs : List String -> Lang cTy (String, Maybe String)
processArgs Nil           = raise NoFileError
processArgs [x]           = raise NoFileError
processArgs [x,y]         = pure (y, Nothing)
processArgs (x::y::z::xs) = pure (y, Just z)

-- ------------------------------------------------------------------ [ Pretty ]

showRes : (GoalNode -> String) -> EvalResult -> Lang cTy ()
showRes pfunc res =
    case toString res pfunc of
      Nothing  => raise BadModelError
      Just res => putStrLn res

-- --------------------------------------------------------------------- [ EOF ]
