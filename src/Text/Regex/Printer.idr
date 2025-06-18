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

data OpPri = Alt | Conseq | Postfix

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

export
Regex RegExpText where
  sym' f = ?foo_sym

  char = RET Postfix . singleton

  anyChar = RET Postfix "."
  sol     = RET Postfix "^"
  eol     = RET Postfix "$"

  wordBoundary True  True  = RET Postfix "\b"
  wordBoundary True  False = RET Postfix "\<"
  wordBoundary False True  = RET Postfix "\>"
  wordBoundary False False = RET Postfix "\B"

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
