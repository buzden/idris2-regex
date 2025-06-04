module Test

import Text.Regex.Naive

import Language.Reflection

%default total

record TestCase where
  constructor T
  {0 tcty : Type}
  {auto showTy : Show tcty}
  regex : Regex tcty
  inputs : LazyList String

printAll : {0 res : _} ->
           (forall s, t. Show t => Show $ res s t) =>
           (forall ty. Regex ty -> (s : String) -> LazyList $ res s ty) ->
           LazyList TestCase ->
           IO ()
printAll sut = Lazy.traverse_ $ \(T {regex, inputs, _}) => do
  putStrLn "\n- regex: \{show @{LowLevel} regex}"
  Lazy.for_ inputs $ \input => do
    putStrLn "\n  - input string: \"\{input}\":"
    let result@(_::_) = sut regex input
      | [] => putStrLn "      <none>"
    Lazy.for_ result $
      putStrLn . ("    - " ++) . show

ab : Regex $ HList [Char, Char]
ab = all [char 'a', char 'b']

a_b : Regex (List Char, Char)
a_b = [| (rep (char 'a'), char 'b') |]

abc : Regex String
abc = string "abc"

main : IO ()
main = printAll (\r, s => rawMatch r $ unpack s)
  [ T (char 'a') ["a", "ab"]
  , T (all [char 'a']) ["a", "ab"]

  , T ab ["ab", "aba", "abb"]

  , T eol ["", "abc"]
  , T sol ["", "abc"]

  , T abc ["0abc1", "abc1", "bc1", "0abc", "0ab"]

  , T a_b ["aaab", "aab", "ab", "b", ""]

  , T (let x = exists [exists [char 'a', pure ()], char 'b'] in all [x, x]) ["abab", "baba"]

  , T (rep ab) ["aabab", "abab", "aba", "ab", "b", ""]

  , T (rep a_b) ["aaab", "aab", "ab", "b", ""]

  , T (rep $ all [rep (char 'a'), char 'b']) ["aaab", "aab", "ab", "b", ""]
  , T (rep $ all [rep1 (char 'a'), char 'b']) ["aaab", "aab", "ab", "b", ""]
  , T (rep $ all [char 'a', rep (char 'a'), char 'b']) ["aaab", "aab", "ab", "b", ""]
  , T (rep $ all [rep (char 'a'), char 'a', char 'b']) ["aaab", "aab", "ab", "b", ""]

  , T (rep $ exists [rep (char 'a'), char 'b']) ["aaab", "aab", "ab", "b", ""]
  , T (rep $ exists [rep $ char 'a', rep $ sym $ const False, char 'b']) ["aaab", "aab", "ab", "b", ""]
  , T (rep $ exists [rep $ char 'a', empty {a=()}, char 'b']) ["aaab", "aab", "ab", "b", ""]
  ]
