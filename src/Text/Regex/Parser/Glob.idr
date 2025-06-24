module Text.Regex.Parser.Glob

import Data.List

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
lexGlob orig with (length orig)
  _ | orL = go [<] orig where
    go : SnocList GlobLex -> List Char -> Either BadRegex $ SnocList GlobLex
    go acc []               = pure acc
    go acc ('\\'::x  :: xs) = go (pushChar x acc) xs
    go acc ('?'      :: xs) = go (acc :< AnyC) xs
    go acc ('*'::'*' :: xs) = go (acc :< AnySS) xs
    go acc ('*'      :: xs) = go (acc :< AnyS) xs
    go acc xxs@('['  :: xs) = do let uc = uncons' xs
                                 let positive = let h = map fst uc in h /= Just '^' && h /= Just '!'
                                 (rest, cs) <- parseCharsSet (orL `minus` length xxs) orL True [<] $ fromMaybe xs $ map snd uc
                                 go (acc :< Cs positive cs) $ assert_smaller xs rest
    go acc (x        :: xs) = go (pushChar x acc) xs

export %inline
parseGlob : Regex rx => String -> Either BadRegex $ rx String
parseGlob = map (composeRx []) . lexGlob . unpack where
  nonDirChar : rx Char
  nonDirChar = sym (/= '/')
  composeRx : All rx tys -> SnocList GlobLex -> rx String
  composeRx acc [<]             = matchOf $ all acc
  composeRx acc (sx :< S [<])   = composeRx acc sx
  composeRx acc (sx :< S [<c])  = composeRx (char c :: acc) sx
  composeRx acc (sx :< S sc)    = composeRx (string (pack $ toList sc) :: acc) sx
  composeRx acc (sx :< AnyC)    = composeRx (nonDirChar :: acc) sx
  composeRx acc (sx :< AnyS)    = composeRx (rep nonDirChar :: acc) sx
  composeRx acc (sx :< AnySS)   = composeRx (rep (anyChar Text) :: acc) sx
  composeRx acc (sx :< Cs p cs) = composeRx (bracketMatcher p cs :: acc) sx
