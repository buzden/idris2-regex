module Text.Regex.Parser

import public Data.Either
import public Data.DPair

import public Language.Reflection

import public Text.Regex.Interface

%default total

public export
data BadRegex : Type where
  RegexIsBad : (index : Nat) -> (reason : String) -> BadRegex

data Chars
  = One Char
  | Class CharClass
  | Range Char Char

data RxLex
  = C Char
  | S String
  | Cs Bool (List Chars) -- [...] and [^...], bool `False` for `[^...]`
  | Group Bool (List RxLex) -- (...) and (?:...), bool `True` for matching group
  | SOL -- ^
  | EOL -- $
  | Alt (List RxLex) (List RxLex) -- |
  | AnyC -- .
  | Rep0 -- *
  | Rep1 -- +
  | Opt -- ?
  | RepN_ Nat -- {n,}
  | RepNM Nat Nat -- {n,m}
  | Rep_M Nat -- {,m}

lex : (top : Bool) -> (curr : SnocList RxLex) -> (notYet : SnocList Char) -> List Char -> Either BadRegex $ List RxLex
lex True  curr [<]       [] = pure $ cast curr
lex False curr [<]       [] = Left $ RegexIsBad ?unexpected_end_pos ?unexpected_end_msg
lex top   curr [<k]      [] = pure $ cast $ curr :< C k
lex top   curr ny@(_:<_) [] = pure $ cast $ (curr :<) $ S $ pack $ cast ny
lex top   curr ny (x :: xs) = ?lex_rhs_1
lex top   curr ny (x :: xs) = ?lex_rhs_2
lex top   curr ny (x :: xs) = ?lex_rhs_3
lex top   curr ny (x :: xs) = ?lex_rhs_4
lex top   curr ny (x :: xs) = ?lex_rhs_5
lex top   curr ny (x :: xs) = ?lex_rhs_6
lex top   curr ny (x :: xs) = ?lex_rhs_7

parseRegex' : Regex rx => List Char -> Either BadRegex $ Exists rx

export %inline
parseRegex : Regex rx => String -> Either BadRegex $ Exists rx
parseRegex = parseRegex' . unpack

public export %inline
toRegex : Regex rx => (s : String) -> (0 _ : IsRight $ parseRegex {rx} s) => rx $ fst $ fromRight $ parseRegex {rx} s
toRegex s = snd $ fromRight $ parseRegex {rx} s

export %macro
(.rx) : Regex rx => String -> Elab $ rx a
(.rx) str = do
  let Right $ Evidence ty r = parseRegex {rx} str
    | Left (RegexIsBad idx reason) => do failAt (getFC !(quote str)) "Bad regular expression at position \{show idx}: \{reason}"
  Just Refl <- catch $ check {expected = a = ty} `(Refl)
    | Nothing => do fail "Unable to match expected type \{show !(quote a)} with the regex type \{show !(quote ty)}"
  pure r
