module Text.Regex.Parser

import public Data.DPair

import public Language.Reflection

import public Text.Regex.Interface

%default total

public export
data BadRegex : Type where
  RegexIsBad : (index : Nat) -> (reason : String) -> BadRegex

export
parseRegex' : Regex rx => List Char -> Either BadRegex $ Exists rx

public export %inline
parseRegex : Regex rx => String -> Either BadRegex $ Exists rx
parseRegex = parseRegex' . unpack

export %macro
fromString : Regex rx => String -> Elab $ rx a
fromString str = do
  let Right $ Evidence ty r = parseRegex {rx} str
    | Left (RegexIsBad idx reason) => do failAt (getFC !(quote str)) "Bad regular expression at position \{show idx}: \{reason}"
  Just Refl <- catch $ check {expected = a = ty} `(Refl)
    | Nothing => do fail "Unable to match expected type \{show !(quote a)} with the regex type \{show !(quote ty)}"
  pure r
