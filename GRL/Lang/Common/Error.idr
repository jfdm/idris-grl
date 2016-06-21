-- --------------------------------------------------------------- [ Error.idr ]
-- Module    : Error.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Common code for all DSML DSLs
module GRL.Lang.Common.Error

%access public export
-- ------------------------------------------------------------------ [ Errors ]

data GError : Type where
  NoFileError      : GError
  NoSuchFileError  : String -> GError
  ParserError      : String -> String -> GError
  NoSuchIdentError : String -> GError
  BadModelError    : GError

Show GError where
  show (NoFileError)            = "File Must Be specified"
  show (NoSuchFileError fn)     = unwords ["No such file:", show fn]
  show (ParserError fn err)     = unlines [unwords ["Unable to parse", show fn, "because:"], err]
  show (NoSuchIdentError ident) = unwords ["No such identifier:", show ident]
  show (BadModelError)          = "Bad Model"

-- --------------------------------------------------------------------- [ EOF ]
