module Test

import Text.Regex

%default total

DottedId = #"\w+(\.\w+)*"#.erx

m0 : MatchesWhole DottedId "cd"
m0 = %search

m1 : MatchesWhole DottedId "cd.cd"
m1 = %search

m2 : MatchesWhole DottedId "cd.a.cd"
m2 = %search
