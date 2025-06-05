module Text.Regex.Parser

import public Data.Either
import public Data.DPair

import public Language.Reflection

import public Text.Regex.Interface

%default total

public export
data BadRegex : Type where
  RegexIsBad : (index : Nat) -> (reason : String) -> BadRegex

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
