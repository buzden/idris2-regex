module Text.Regex.Printer

import Data.String

import Derive.Eq
import Derive.Ord

import Language.Reflection
import Language.Reflection.Derive
import Language.Reflection.Syntax
import Language.Reflection.Types

import Text.Regex.Interface

%default total
%language ElabReflection

data OpPri = Alt | Conseq | Postfix | Symbol

%runElab derive `{OpPri} [Eq, Ord]

export
data RegExpText a = RET OpPri String

tostr : (context : OpPri) -> RegExpText a -> String
tostr outer $ RET inner s = if outer > inner then "(?:\{s})" else s

export
Functor RegExpText where
  map _ $ RET p s = RET p s

export
Applicative RegExpText where
  pure _ = RET Conseq ""
  l <*> r = RET Conseq $ tostr Conseq l <+> tostr Conseq r

export
Alternative RegExpText where
  empty = RET Alt "$_^"
  l <|> r = RET Alt "\{tostr Alt l}|\{tostr Alt r}"

toHex : Int -> String
toHex = pack . go [] where
  ord0, ordA : Int
  ord0 = ord '0'
  ordA = ord 'A'
  go : List Char -> Int -> List Char
  go acc n = do
    let n' = n `div` 16
    let r = n `mod` 16
    let c = chr $ r + if r < 10 then ord0 else ordA
    let acc = c :: acc
    if n' > 0 then go acc $ assert_smaller n n' else acc

printChar : Char -> String
printChar '\n' = #"\n"#
printChar '\r' = #"\r"#
printChar '\t' = #"\t"#
printChar '\f' = #"\f"#
printChar '\v' = #"\v"#
printChar '\a' = #"\a"#
printChar '\\' = #"\\"#
printChar c = let ordC = ord c in
  if 0x20 <= ordC && ordC <= 0x7E then singleton c
    else if ordC <= 0xFF then "\\x\{toHex $ ordC `div` 16}\{toHex $ ordC `mod` 16}"
      else "\\x{\{toHex ordC}}"

test127 : (Char -> Bool) -> Vect 127 Bool
test127 f = allFins _ <&> f . chr . cast . finToNat

searchClasses : List (String, Vect 127 Bool)
searchClasses = ?searchClasses_rhs

export
Regex RegExpText where
  sym' f = ?foo_sym

  char = RET Symbol . singleton

  anyChar = RET Symbol "."
  sol     = RET Symbol "^"
  eol     = RET Symbol "$"

  wordBoundary True  True  = RET Symbol "\b"
  wordBoundary True  False = RET Symbol "\<"
  wordBoundary False True  = RET Symbol "\>"
  wordBoundary False False = RET Symbol "\B"

  string = RET Conseq

  withMatch $ RET p s = RET p s
  matchOf   $ RET p s = RET p s

  exists []        = empty
  exists [RET p s] = RET p s
  exists rs        = RET Alt $ joinBy "|" $ forget $ mapProperty (tostr Alt) rs

  opt  r = RET Postfix "\{tostr Postfix r}?"
  rep  r = RET Postfix "\{tostr Postfix r}*"
  rep1 r = RET Postfix "\{tostr Postfix r}+"
  repeatN       n r = RET Postfix "\{tostr Postfix r}{\{show n}}"
  repeatAtLeast n r = RET Postfix "\{tostr Postfix r}{\{show n},}"
  repeatAtMost  n r = RET Postfix "\{tostr Postfix r}{,\{show n}}"
  repeatNM    n m r = RET Postfix "\{tostr Postfix r}{\{show n},\{show m}}"

export
Interpolation (RegExpText a) where
  interpolate $ RET _ s = s
