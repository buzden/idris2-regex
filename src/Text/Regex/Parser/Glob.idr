module Text.Regex.Parser.Glob

import public Data.DPair

import public Text.Regex.Interface
import public Text.Regex.Parser

import Data.SnocList

%default total

data GlobLex
  = S (SnocList Char)
  | AnyC
  | AnyS
  | AnySS
  | Cs Bool (List BracketChars) -- [...] and [!...]/[^...], bool `False` for [!...]/[^...]

pushChar : Char -> SnocList GlobLex -> SnocList GlobLex
pushChar c (sx :< S cs) = sx :< S (cs :< c)
pushChar c sx           = sx :< S (pure c)

lexGlob : List Char -> Either BadRegex $ SnocList GlobLex
lexGlob orig = go [<] orig where
  orL : Nat
  orL = length orig
  pos : (left : List Char) -> Nat
  pos xs = orL `minus` length xs
  go : SnocList GlobLex -> List Char -> Either BadRegex $ SnocList GlobLex
  go acc [] = pure acc
  go acc ('\\'::x  :: xs) = go (pushChar x acc) xs
  go acc ('?'      :: xs) = go (acc :< AnyC) xs
  go acc ('*'::'*' :: xs) = go (acc :< AnySS) xs
  go acc ('*'      :: xs) = go (acc :< AnyS) xs
  go acc xxs@('['::'!' :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (acc :< Cs False cs) $ assert_smaller xs rest
  go acc xxs@('['::'^' :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (acc :< Cs False cs) $ assert_smaller xs rest
  go acc xxs@('['      :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (acc :< Cs True  cs) $ assert_smaller xs rest
  go acc (x :: xs) = go (pushChar x acc) xs

export %inline
parseGlob : Regex rx => String -> Either BadRegex $ rx String
--parseGlob = map (\r => matchOf r.snd) . parseGlob' . unpack
