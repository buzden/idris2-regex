module Text.Regex.Parser.Glob

import public Data.DPair

import public Text.Regex.Interface
import public Text.Regex.Parser

%default total

data GlobLex
  = S String
  | AnyC
  | AnyS
  | AnySS
  | Cs Bool (List BracketChars)

lexGlob : List Char -> Either BadRegex $ SnocList GlobLex
lexGlob = go [<] where
  go : SnocList GlobLex -> List Char -> Either BadRegex $ SnocList GlobLex
  go acc [] = ?parseGlob_rhs_0
  go acc ('\\'::x :: xs) = ?parseGlob_rhs_1
  go acc xxs@('['::'^' :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => parseGlob' $ assert_smaller xs rest
  go acc xxs@('['      :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (push ctx $ Cs True  cs) $ assert_smaller xs rest
  go acc (x :: xs) = ?parseGlob_rhs_2
  go acc (x :: xs) = ?parseGlob_rhs_3
  go acc (x :: xs) = ?parseGlob_rhs_4
  go acc (x :: xs) = ?parseGlob_rhs_5
  go acc (x :: xs) = ?parseGlob_rhs_6
  go acc (x :: xs) = ?parseGlob_rhs_7

export %inline
parseGlob : Regex rx => String -> Either BadRegex $ rx String
--parseGlob = map (\r => matchOf r.snd) . parseGlob' . unpack
