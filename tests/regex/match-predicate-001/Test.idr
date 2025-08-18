module Test

import Text.Regex

data FancyString : Type where
  MkFStr : (str : String) -> (0 _ : MatchesWhole ("1.*2|21".erx <|> the (RegExp _) "21".erx <|> the (RegExp _) "21".erx) str) => FancyString

fs1 : FancyString
fs1 = MkFStr "12"

fs2 : FancyString
fs2 = MkFStr "1ab2"

fs3 : FancyString
fs3 = MkFStr "21"

data FancierString : Type where
  MkFerStr : (str : String) -> (0 _ : MatchesInside ("1.*2|21".erx <|> the (RegExp _) "21".erx <|> the (RegExp _) "21".erx) str) => FancierString

fers1 : FancierString
fers1 = MkFerStr "12"

fers2 : FancierString
fers2 = MkFerStr "1ab2"

fers3 : FancierString
fers3 = MkFerStr "21"

fers3' : FancierString
fers3' = MkFerStr "abc21cab"

fers2' : FancierString
fers2' = MkFerStr "ca1ab2cc"
