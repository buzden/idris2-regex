module Test

import Text.Regex
import Text.Regex.Printer

%default total

record TestCase where
  constructor T
  {0 tcty : Type}
--  {auto showTy : Show tcty}
  regex : forall rx. Regex rx => rx tcty
  inputs : LazyList String

runAll : LazyList TestCase -> IO ()
runAll = Lazy.traverse_ $ \(T {regex, inputs, _}) => do
  putStrLn "\n- regex: \{regex {rx=RegExpText}}"
  Lazy.for_ inputs $ \input => do
    putStrLn "\n  - input string: \{show input}:"
    Lazy.for_ [True, False] $ \multiline => do
      putStr "\n    - \{the String $ if multiline then "multiline" else "single-line"} mode:\n      "
      printLn $ forgetVal <$> matchInside {multiline} regex input

main : IO ()
main = runAll
  [ T "a.*$".erx ["mama\namam"]
  , T "[abc]+(a|b|c)".erx ["aa"]
  ]
