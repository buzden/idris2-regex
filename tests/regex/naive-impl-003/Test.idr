module Test

import Text.Regex

%default total

rx : RegExp ?
rx = "[abc]+(a|b|c)".erx

str : String
str = "aa"

main : IO ()
main = for_ [True, False] $ \multiline => do
  putStrLn "Multiline: \{show multiline}"
  printLn $ forgetVal <$> matchInside {multiline} rx str
