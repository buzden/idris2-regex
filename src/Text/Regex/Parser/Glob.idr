module Text.Regex.Parser.Glob

import public Data.DPair

import public Text.Regex.Interface
import public Text.Regex.Parser

%default total

parseGlob' : Regex rx => List Char -> Either BadRegex $ Exists rx

export %inline
parseGlob : Regex rx => String -> Either BadRegex $ rx String
parseGlob = map (\r => matchOf r.snd) . parseGlob' . unpack
