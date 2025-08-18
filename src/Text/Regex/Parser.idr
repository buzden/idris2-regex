module Text.Regex.Parser

import Data.Bits
import Data.List
import Data.SnocList

import Text.Regex.Interface

%default total

------------------
--- Error type ---
------------------

public export
data BadRegex : Type where
  RegexIsBad : (index : Nat) -> (reason : String) -> BadRegex

---------------------------
--- Bracket expressions ---
---------------------------

data BracketChars
  = One Char
  | RangeOpen Char
  | Class Bool CharClass -- False means negation of this char class
  | Range Char Char

public export
matchesBracket : Char -> BracketChars -> Bool
matchesBracket c $ One k       = c == k
matchesBracket c $ RangeOpen k = c == k
matchesBracket c $ Class nn cl = nn == charClass cl c
matchesBracket c $ Range l r   = l <= c && c <= r

%inline
public export
bracketMatcher : Regex rx => Foldable f => (positive : Bool) -> f BracketChars -> rx Char
bracketMatcher p cs = sym (\c => p == any (matchesBracket c) cs)

public export
baseNumDescr : (base : Nat) -> String
baseNumDescr 10 = "decimal"
baseNumDescr 16 = "hexadecimal"
baseNumDescr 2  = "binary"
baseNumDescr 8  = "octal"
baseNumDescr b  = "\{show b}-base"

public export
parseNat : (base : Nat) -> (0 _ : So $ 2 <= base && base <= 36) => {default Z acc : Nat} -> (pos : Lazy Nat) -> List Char -> Either BadRegex Nat
parseNat base pos [] = Left $ RegexIsBad pos "a \{baseNumDescr base} number is expected"
parseNat base pos (x::xs) = do
  let Just n = parseDigit base x
    | Nothing => Left $ RegexIsBad pos "bad \{baseNumDescr base} number"
  let acc = acc * base + cast n
  case xs of
    [] => pure acc
    _  => parseNat base {acc} (S pos) xs

-- We treat `\` inside `[...]` more like PCRE rather than POSIX ERE.
-- However, we do not *require* `\` itself to be quoted, it is understood literally if does not form a special character.
public export
parseCharsSet : (startLen, origLen : Lazy Nat) -> (start : Bool) -> SnocList BracketChars -> List Char -> Either BadRegex (List Char, List BracketChars)
parseCharsSet stL orL start curr [] = Left $ RegexIsBad stL "unmatched opening square bracket"
parseCharsSet stL orL False curr (']' :: xs) = pure (xs, cast curr)
parseCharsSet stL orL start curr $ '\\'::'n' :: xs = parseCharsSet stL orL False (curr :< One '\n') xs
parseCharsSet stL orL start curr $ '\\'::'r' :: xs = parseCharsSet stL orL False (curr :< One '\r') xs
parseCharsSet stL orL start curr $ '\\'::'t' :: xs = parseCharsSet stL orL False (curr :< One '\t') xs
parseCharsSet stL orL start curr $ '\\'::'f' :: xs = parseCharsSet stL orL False (curr :< One '\f') xs
parseCharsSet stL orL start curr $ '\\'::'v' :: xs = parseCharsSet stL orL False (curr :< One '\v') xs
parseCharsSet stL orL start curr $ '\\'::'0' :: xs = parseCharsSet stL orL False (curr :< One '\0') xs
parseCharsSet stL orL start curr $ '\\'::'a' :: xs = parseCharsSet stL orL False (curr :< One '\a') xs
parseCharsSet stL orL start curr $ '\\'::'\\':: xs = parseCharsSet stL orL False (curr :< One '\\') xs
parseCharsSet stL orL start curr $ '\\'::'w' :: xs = parseCharsSet stL orL False (curr :< Class True  Word) xs
parseCharsSet stL orL start curr $ '\\'::'W' :: xs = parseCharsSet stL orL False (curr :< Class False Word) xs
parseCharsSet stL orL start curr $ '\\'::'s' :: xs = parseCharsSet stL orL False (curr :< Class True  Space) xs
parseCharsSet stL orL start curr $ '\\'::'S' :: xs = parseCharsSet stL orL False (curr :< Class False Space) xs
parseCharsSet stL orL start curr $ '\\'::'d' :: xs = parseCharsSet stL orL False (curr :< Class True  Digit) xs
parseCharsSet stL orL start curr $ '\\'::'D' :: xs = parseCharsSet stL orL False (curr :< Class False Digit) xs
parseCharsSet stL orL start curr $ '\\'::'x'::'{' :: xs = do
  let (hexes, rest) = span (/= '}') xs
  let '}' :: rest = rest | _ => Left $ RegexIsBad (orL `minus` S (length xs)) "unmatched opening curly bracket"
  n <- parseNat 16 (orL `minus` length xs) hexes
  let True = shiftR (cast {to=Integer} n) 32 == 0 | False => Left $ RegexIsBad (orL `minus` length xs) "we expect no more than a 32-bit hex number"
  parseCharsSet stL orL False (curr :< One (chr $ cast n)) $ assert_smaller xs rest
parseCharsSet stL orL start curr $ '\\'::'x'::ulxs@(u::l :: xs) = do
  n <- parseNat 16 (orL `minus` length ulxs) [u,l]
  parseCharsSet stL orL False (curr :< One (chr $ cast n)) xs
parseCharsSet stL orL start curr xxs@('\\'::'x':: xs) =
  Left $ RegexIsBad (orL `minus` length xxs) "bad hex character command, use formats \xFF or \x{FFF...}"
parseCharsSet stL orL start curr $ '\\'::x :: xs = parseCharsSet stL orL False (curr :< One x) xs
parseCharsSet stL orL start curr $ '['::':'::'u'::'p'::'p'::'e'::'r'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Upper) xs
parseCharsSet stL orL start curr $ '['::':'::'l'::'o'::'w'::'e'::'r'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Lower) xs
parseCharsSet stL orL start curr $ '['::':'::'a'::'l'::'p'::'h'::'a'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Alpha) xs
parseCharsSet stL orL start curr $ '['::':'::'a'::'l'::'n'::'u'::'m'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Alnum) xs
parseCharsSet stL orL start curr $ '['::':'::'d'::'i'::'g'::'i'::'t'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Digit) xs
parseCharsSet stL orL start curr $ '['::':'::'x'::'d'::'i'::'g'::'i'::'t'::':'::']' :: xs = parseCharsSet stL orL False (curr :< Class True XDigit) xs
parseCharsSet stL orL start curr $ '['::':'::'p'::'u'::'n'::'c'::'t'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Punct) xs
parseCharsSet stL orL start curr $ '['::':'::'b'::'l'::'a'::'n'::'k'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Blank) xs
parseCharsSet stL orL start curr $ '['::':'::'s'::'p'::'a'::'c'::'e'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Space) xs
parseCharsSet stL orL start curr $ '['::':'::'c'::'n'::'t'::'r'::'l'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Cntrl) xs
parseCharsSet stL orL start curr $ '['::':'::'g'::'r'::'a'::'p'::'h'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Graph) xs
parseCharsSet stL orL start curr $ '['::':'::'p'::'r'::'i'::'n'::'t'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Print) xs
parseCharsSet stL orL start curr $ '['::':'::'a'::'s'::'c'::'i'::'i'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Ascii) xs
parseCharsSet stL orL start curr $ '['::':'::'w'::'o'::'r'::'d'::':'::']'           :: xs = parseCharsSet stL orL False (curr :< Class True Word) xs
parseCharsSet stL orL start (curr :< RangeOpen l :< One '-') rxs@(r :: xs) = if l <= r -- finish the range operator
  then parseCharsSet stL orL False (curr :< Range l r) xs
  else Left $ RegexIsBad (orL `minus` 1 + length rxs) "invalid range, left is greater than `right"
parseCharsSet stL orL start curr (l::'-' :: xs) = parseCharsSet stL orL False (curr :< RangeOpen l :< One '-') xs -- start the range operator
parseCharsSet stL orL start curr (x :: xs) = parseCharsSet stL orL False (curr :< One x) xs
