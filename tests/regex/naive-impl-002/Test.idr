module Test

import Text.Regex

%default total

rx : RegExp ?
rx = "a.*$".erx

str : String
str = "mama\namam"

main : IO ()
main = for_ [True, False] $ \multiline => do
  putStrLn "Multiline: \{show multiline}"
  printLn $ forgetVal <$> matchInside {multiline} rx str
