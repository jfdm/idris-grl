-- -------------------------------------------------------------- [ Parser.idr ]
-- Module    : Parser.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Common Parsers
module GRL.Lang.Common.Parser

import Lightyear
import Lightyear.Char
import Lightyear.Strings

import GRL.Common

%access export

-- ------------------------------------------------------ [ Parsing Lang Utils ]

comment : String -> String -> String -> Parser ()
comment l b e = (line l    *> pure ())
            <|> (block b e *> pure ())
            <|> spaces
            <?> "Comment"
    where
      line : String -> Parser String
      line l = do
          token l
          doc <- manyTill anyChar endOfLine
          spaces
          pure $ pack doc
        <?> "Line comment"

      block : String -> String -> Parser String
      block b e = do
          token b
          doc <- manyTill anyChar (token e)
          spaces
          pure $ pack doc
        <?> "Block Comment"

keyword : String -> Parser ()
keyword s = do
    string s
    spaces
    pure ()
  <?> "Keywords"

ident : Parser String
ident = lexeme (map pack $ some identChar) <?> "Identity"
  where
    identChar : Parser Char
    identChar = alphaNum <?> "Ident Char"

-- ------------------------------------------------------------ [ GLang Parser ]

gComment : Parser ()
gComment = comment "--" "{-" "-}" <?> "Comment"


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

-- --------------------------------------------------------------------- [ EOF ]
