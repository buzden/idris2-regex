module Text.Regex.Printer

import Data.String
import Data.Vect.Extra

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
  empty = RET Conseq "\b\B"
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

-- sorted from big to small
searchPosixClasses : List (String, Vect 127 Bool)
searchPosixClasses = map @{Compose} (test127 . charClass) $
  [ ("print", Print), ("graph", Graph), ("alnum", Alnum), ("alpha", Alpha), ("upper", Upper), ("lower", Lower)
  , ("xdigit", XDigit), ("digit", Digit), ("punct", Punct) , ("cntrl", Cntrl), ("space", Space), ("blank", Blank) ]

findAndCut : (a -> Bool) -> List a -> Maybe (List a, a)
findAndCut f []      = Nothing
findAndCut f (x::xs) = if f x then Just (xs, x) else findAndCut f xs

-- we can treat `a <= b` as logical implication of `a` to `b` when they're `Bool`s
calcPosClass : Vect 127 Bool -> (SnocList String, Vect 127 Bool)
calcPosClass orig = go searchPosixClasses orig [<] where
  go : List (String, Vect 127 Bool) -> Vect 127 Bool -> SnocList String -> (SnocList String, Vect 127 Bool)
  go spc curr acc = case findAndCut (\(_, vs) => all (\(v, o) => v <= o) (zip vs orig) && any (\(v, c) => v && c) (zip vs curr)) spc of
    Just (spc, name, vs) => go spc (assert_smaller curr $ zipWith (\c, v => c && not v) curr vs) (acc :< name)
    Nothing => (acc, curr)

calcClass : Vect 127 Bool -> RegExpText a
calcClass vs = do
  let (pcls, pvs) = calcPosClass vs
  let (ncls, nvs) = calcPosClass $ not <$> vs
  let (pn, nn) = mapHom (let _ = Monoid.Additive in foldMap $ \b => if b then 1 else 0) (pvs, nvs)
  let (neg, cls, vs) = if pn <= nn then (False, pcls, pvs) else (True, ncls, nvs)
  let fin = concatMap (\cl => "[:\{cl}:]") cls ++ concatMap (\(b, n) => if b then printChar (chr $ cast $ finToNat n) else "") (toListI vs)
  if length fin == 0 then empty else
    if neg || length fin > 1
      then let neg : String := if neg then "^" else "" in RET Symbol "[\{neg}\{fin}]"
      else RET Symbol fin

export
Regex RegExpText where
  -- this implementation only takes behaviour on ASCII symbols into account
  sym' = calcClass . test127 . (isJust .)
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
