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
  withMatch : rx a -> rx (String, a)

  rep1 : rx a -> rx $ List1 a
  rep1 r = [| r ::: rep r |]
  rep : rx a -> rx $ List a
  rep r = toList <$> rep1 r <|> pure []

  ||| Matches a symbol satisfying the given predicate, and returns the matched char, or fails.
  sym : (Char -> Bool) -> rx Char
  ||| Matches the given symbol and returns it, or fails.
  char : Char -> rx Char
  char = sym . (==)

  ||| Matches the start of the line/text
  sol : rx ()
  ||| Matches the end of the line/text
  eol : rx ()

  string : String -> rx String
  string = map pack . sequence . map char . unpack

||| Matches all of given sub-regexes, sequentially.
public export %inline
all : Regex rx => All rx tys -> rx $ HList tys
all = pushOut

-- TODO to reimplement with upstream function, when it's added
||| Matches is there exists at least one sub-regex that matches.
export
exists : Regex rx => All rx tys -> rx $ Any Prelude.id tys
exists []      = empty
exists (r::rs) = Here <$> r <|> There <$> exists rs

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
data PosixCharClass
  = Alpha | Digit | XDigit | Alnum | Upper | Lower | Word | NonWord
  | Cntrl | Space | Blank | Graph | Ascii | Punct

export
posix : Regex rx => PosixCharClass -> rx Char
posix Alpha   = sym isAlpha
posix Digit   = sym isDigit
posix XDigit  = sym isHexDigit
posix Alnum   = sym isAlphaNum
posix Upper   = sym isUpper
posix Lower   = sym isLower
posix Word    = sym $ \c => isAlphaNum c || c == '_'
posix NonWord = sym $ \c => not $ isAlphaNum c || c == '_'
posix Cntrl   = sym isControl
posix Space   = sym isSpace
posix Blank   = anyOf [' ', '\t']
posix Graph   = (between `on` chr) 0x21 0x7E
posix Ascii   = (between `on` chr) 0x00 0x7F
posix Punct   = sym $ \c => let k = ord c in (0x21 <= k && k <= 0x7E) && not (isSpace c) && not (isAlphaNum c)

----------------------
--- Regex matching ---
----------------------

namespace Match

  public export
  record OneMatchInside a where
    constructor MkOneMatchInside
    unmatchedPre  : String
    matchedStr    : String
    matchedVal    : a
    unmatchedPost : String

  public export
  data AllMatchedInside : Type -> Type where
    Stop  : (post : String) -> AllMatchedInside a
    Match : (pre : String) -> (matched : String) -> a -> (cont : AllMatchedInside a) -> AllMatchedInside a

  public export
  matchedCnt : AllMatchedInside a -> Nat
  matchedCnt $ Stop {}         = Z
  matchedCnt $ Match {cont, _} = S $ matchedCnt cont

public export
interface RegexMatcher rx where
  matchWhole  : rx a -> String -> Maybe a
  matchInside : rx a -> String -> Maybe $ OneMatchInside a
  matchAll    : rx a -> String -> AllMatchedInside a


