module Text.Regex.Interface

import public Data.Alternative
import Data.List
import public Data.List.Quantifiers
import public Data.List1
import public Data.Vect

import Deriving.Show

%default total
%language ElabReflection

----------------------
--- Regex building ---
----------------------

public export
data EdgeSide = Start | End
||| `Line` line mode means "depends on the matching mode", `Text` means "literally, independent on matching mode".
public export
data LineMode = Line | Text

export %hint ShowEdgeSide : Show EdgeSide; ShowEdgeSide = %runElab derive
export %hint ShowLineMode : Show LineMode; ShowLineMode = %runElab derive

public export
interface Alternative rx => Regex rx where
  ||| Matches a symbol if the given function returns `Just`, and returns the contents of this `Just`.
  sym' : (Char -> Maybe a) -> rx a
  ||| Matches a symbol satisfying the given predicate, and returns the matched char, or fails.
  sym : (Char -> Bool) -> rx Char
  sym f = sym' $ \c => whenT (f c) c
  ||| Matches the given symbol and returns it, or fails.
  char : Char -> rx Char
  char = sym . (==)

  ||| Matches any single char in line (i.e. without newlines depending on the mode) or in text (i.e. literally any character).
  anyChar : LineMode -> rx Char

  ||| Matches the start/end of the line/text.
  edge : LineMode -> EdgeSide -> rx ()

  ||| Zero-width boundary between a word-class char and a non-word class char or an edge.
  |||
  ||| For left or right boundary, set corresponding bool parameter to `True`,
  ||| for any set both to `True`, for non-boundary set both to `False`.
  wordBoundary : (left : Bool) -> (right : Bool) -> rx ()

  ||| Matches the given string.
  string : String -> rx String
  string = map pack . sequence . map char . unpack

  ||| Regex having an original matched string along with the original value.
  withMatch : rx a -> rx (String, a)
  ||| Regex having only the original matched string as a contained resulting value.
  matchOf : rx a -> rx String
  matchOf = map fst . withMatch

  ||| Matches all of given sub-regexes, sequentially.
  all : All rx tys -> rx $ HList tys
  all = pushOut

  ||| Matches is there exists at least one sub-regex that matches.
  exists : All rx tys -> rx $ Any Prelude.id tys
  exists = altAll

  ||| Optional application of a given regex.
  opt : rx a -> rx $ Maybe a
  opt = optional

  rep1 : rx a -> rx $ List1 a
  rep1 r = [| r ::: rep r |]
  rep : rx a -> rx $ List a
  rep r = toList <$> rep1 r <|> pure []

  repeatN : (n : Nat) -> rx a -> rx $ Vect n a
  repeatN n = sequence . replicate n

  repeatNOrMore : (n : Nat) -> rx a -> rx $ List a
  repeatNOrMore n r = [| map toList (repeatN n r) ++ rep r |]

  repeatNOrLess : (n : Nat) -> rx a -> rx $ List a
  repeatNOrLess Z     _ = pure []
  repeatNOrLess (S n) r = [| r :: repeatNOrLess n r |] <|> pure []

  repeatNM : (n, m : Nat) -> (0 nm : n `LTE` m) => rx a -> rx $ List a
  repeatNM n m r = [| map toList (repeatN n r) ++ repeatNOrLess (m `minus` n) r |]

--- Special general cases ---

||| Always matches without consuming any symbol.
public export %inline
omega : Regex rx => rx ()
omega = pure ()

export infixr 7 `thenGoes`
||| Simple consequent composition
public export %inline
thenGoes : Regex rx => rx a -> rx b -> rx (a, b)
thenGoes x y = [| (x, y) |]

--- Special chars ---

public export %inline
anyOf : Regex rx => List Char -> rx Char
anyOf cs = sym (`elem` cs)

public export %inline
noneOf : Regex rx => List Char -> rx Char
noneOf cs = sym $ not . (`elem` cs)

public export %inline
between : Regex rx => Char -> Char -> rx Char
between l r = sym $ \k => l <= k && k <= r

||| Either "\r\n" or any of '\n', '\r' or '\v'
public export
genericNL : Regex rx => rx String
genericNL = string "\x0d\x0a" <|> map singleton (anyOf ['\n', '\r', '\v'])

public export
data CharClass
  = Alpha | Digit | XDigit | Alnum | Upper | Lower | Word
  | Cntrl | Space | Blank | Graph | Print | Ascii | Punct

public export %tcinline
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

--- Special combinations ---

public export
parseDigit : (base : Nat) -> (0 _ : So (2 <= base && base <= 36)) => Char -> Maybe $ Fin base
parseDigit base@(S _) c = do
  let tofin = \n => fromMaybe FZ {- must never happen -} $ integerToFin (cast n) base
  let ord0 = ord '0'
  let ordA = ord 'a'
  let c = if isUpper c then chr (ord c - ord 'A' + ordA) else c
  let pred = if base <= 10
               then let upDig = chr $ ord0 + cast base              in '0' <= c && c <= upDig
               else let upLet = chr $ ordA + cast (base `minus` 10) in '0' <= c && c <= '9' || 'a' <= c && c <= upLet
  whenT pred $ tofin $ if c <= '9' then ord c - ord0 else ord c - ordA + 10

||| A digit of given base
public export
digit' : Regex rx => (base : Nat) -> (0 _ : So (2 <= base && base <= 36)) => rx $ Fin base
digit' base = sym' $ parseDigit base

||| A 10-base digit
public export %inline
digit : Regex rx => rx $ Fin 10
digit = digit' 10

||| A natural number regex without any sign
public export
naturalNumber' : Regex rx => (base : Nat) ->  (0 _ : So (2 <= base && base <= 36)) => rx Nat
naturalNumber' base = rep1 (digit' base) <&> \(h:::tl) => go (cast h) tl where
  go : Nat -> List (Fin base) -> Nat
  go acc []      = acc
  go acc (x::xs) = go (acc * base + cast x) xs

public export %inline
naturalNumber : Regex rx => rx Nat
naturalNumber = naturalNumber' 10
