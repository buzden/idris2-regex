module Text.Regex.Interface

import Data.List
import public Data.List.Quantifiers
import public Data.List1
import public Data.Vect

%default total

----------------------
--- Regex building ---
----------------------

public export
interface Alternative rx => Regex rx where
  ||| Matches a symbol satisfying the given predicate, and returns the matched char, or fails.
  sym : (Char -> Bool) -> rx Char
  ||| Matches the given symbol and returns it, or fails.
  char : Char -> rx Char
  char = sym . (==)

  ||| Matches the start of the line/text
  sol : rx ()
  ||| Matches the end of the line/text
  eol : rx ()

  ||| Zero-width boundary between a word-class char and a non-word class char or an edge.
  |||
  ||| For left or right boundary, set corresponding bool parameter to `True`,
  ||| for any set both to `True`, for non-boundary set both to `False`.
  wordBoundary : (left : Bool) -> (right : Bool) -> rx ()

  string : String -> rx String
  string = map pack . sequence . map char . unpack

  withMatch : rx a -> rx (String, a)

  ||| Matches all of given sub-regexes, sequentially.
  all : All rx tys -> rx $ HList tys
  all = pushOut

  ||| Matches is there exists at least one sub-regex that matches.
  exists : All rx tys -> rx $ Any Prelude.id tys
  exists = altAll

  rep1 : rx a -> rx $ List1 a
  rep1 r = [| r ::: rep r |]
  rep : rx a -> rx $ List a
  rep r = toList <$> rep1 r <|> pure []

--- Special general cases ---

||| Always matches without consuming any symbol.
export %inline
omega : Regex rx => rx ()
omega = pure ()

export %inline
matchedOf : Regex rx => rx a -> rx String
matchedOf = map fst . withMatch

--- Special repetitions ---

export
repeatN : Regex rx => (n : Nat) -> rx a -> rx $ Vect n a
repeatN Z     _ = pure []
repeatN (S Z) r = r <&> pure
repeatN (S n) r = [| r :: repeatN n r |]

export
repeatAtLeast : Regex rx => (n : Nat) -> rx a -> rx $ List a
repeatAtLeast n r = [| map toList (repeatN n r) ++ rep r |]

export
repeatAtMost : Regex rx => (m : Nat) -> rx a -> rx $ List a
repeatAtMost Z     _ = pure []
repeatAtMost (S m) r = [| r :: repeatAtMost m r |] <|> pure []

export
repeatNM : Regex rx => (n, m : Nat) -> (0 _ : n `LTE` m) => rx a -> rx $ List a
repeatNM n m r = [| map toList (repeatN n r) ++ repeatAtMost (m `minus` n) r |]

--- Special chars ---

export %inline
anyChar : Regex rx => rx Char
anyChar = sym $ const True

export %inline
anyOf : Regex rx => List Char -> rx Char
anyOf cs = sym (`elem` cs)

export %inline
noneOf : Regex rx => List Char -> rx Char
noneOf cs = sym $ not . (`elem` cs)

export %inline
between : Regex rx => Char -> Char -> rx Char
between l r = sym $ \k => l <= k && k <= r

public export
data CharClass
  = Alpha | Digit | XDigit | Alnum | Upper | Lower | Word
  | Cntrl | Space | Blank | Graph | Print | Ascii | Punct

export %tcinline
charClass : CharClass -> Char -> Bool
charClass Alpha    = isAlpha
charClass Digit    = isDigit
charClass XDigit   = isHexDigit
charClass Alnum    = isAlphaNum
charClass Upper    = isUpper
charClass Lower    = isLower
charClass Word     = \c => isAlphaNum c || c == '_'
charClass Cntrl    = isControl
charClass Space    = isSpace
charClass Blank    = \c => c == ' ' || c == '\t'
charClass Graph    = \c => chr 0x21 <= c && c <= chr 0x7E
charClass Print    = \c => c == ' ' || charClass Graph c
charClass Ascii    = \c => chr 0x00 <= c && c <= chr 0x7F
charClass Punct    = \c => charClass Graph c && not (isSpace c) && not (isAlphaNum c)
