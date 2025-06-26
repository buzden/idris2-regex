module Test

import Text.Regex.Parser.ERE

%default total

bad_nested_postfix : Regex rx => rx ?
bad_nested_postfix = #"a*?"#.erx
