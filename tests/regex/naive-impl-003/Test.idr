module Test

import Text.Regex
import Text.Regex.Printer

import Hedgehog

import System
import System.File

%default total

data MatchType = Inside | Whole | All

Interpolation MatchType where
  interpolate Inside = "inside"
  interpolate Whole  = "whole"
  interpolate All    = "all"

multi : Bool -> String
multi True  = "multiline"
multi False = "single-line"

--rx : RegExp ?
--rx = #"^(?:[^a-c-d]{,4}?[[:digit:]ab\x4F\x{004f}])+.*+fev\x4F\x{0000000000004F}+"#.erx

delimOutput : Eq a => (delim : List a) -> (n : Nat) -> List a -> Maybe $ Vect n $ List a
delimOutput delim 0 str = Nothing
delimOutput delim 1 str = Just [str]
delimOutput delim (S k) str = do
  (l, _, r) <- infixOfBy (flip whenT () .: (==)) delim str
  (l ::) <$> delimOutput delim k r

theDelim : List Char
theDelim = ['\n'] ++ concat (List.replicate 20 $ unpack "-=~") ++ ['\n']

covering
matchPerl : (regex, str : String) -> Maybe (String, String, String)
matchPerl regex str = do
  let input = """
    $input = q\{show str};
    if ($input =~ /(.*?)(\{regex})/) {
      $post = substr($input, length($1)+length($2));
      $del = "\\n".("-=~"x20)."\\n";
      print "$1$del$2$del$post";
    } else {
      print "no match\\n";
    }
    """
  output <- unsafePerformIO $ do
    --ignore $ fPutStr stderr "\n----\n\{input}\n----\n"
    Right sp <- popen2 "perl" | Left _ => pure Nothing
    Right () <- fPutStr sp.input input | Left _ => pure Nothing
    closeFile sp.input
    Right output <- fRead sp.output | Left _ => pure Nothing
    closeFile sp.output
    exitCode <- popen2Wait sp
    pure $ whenT (exitCode == 0) output
  delimOutput theDelim 3 (unpack output) <&> map pack <&> \[a, b, c] => (a, b, c)

matchNaive : (regex, str : String) -> Maybe (String, String, String)
matchNaive regex str = do
  let Right (Evidence _ r) = parseRegex regex | Left _ => Nothing
  forgetVal <$> matchInside r str

covering
naiveMatchesPerl : (regex : String) -> (PropertyName, Property)
naiveMatchesPerl regex = MkPair (fromString "particular expression \{regex}, inside, single-line mode") $ property $ do
  case parseRegex {rx=RegExpText} regex of
    Right (Evidence _ p) => annotate "\{p}"
    Left (RegexIsBad pos reason) => annotate "regex is bad at \{show pos}: \{reason}"
  str <- forAll $ string (constant 0 100) (char $ constant ' ' '\x7E')
  let mp = matchPerl regex str
  let mn = matchNaive regex str
  classify "perl matched" $ isJust mp
  classify "perl didn't match" $ mp == Nothing
  classify "naive matched" $ isJust mn
  classify "naive didn't match" $ mn == Nothing
  annotateAllShow [mp, mn]
  mp === mn

covering
main : IO ()
main = test
  [ "patricular regular expression" `MkGroup`
    [ naiveMatchesPerl #"[abc]+(a|b|c)"#
    , naiveMatchesPerl #".+(a|b|c)"#
    , naiveMatchesPerl #".+.+.+(a|b|c)"#
    , naiveMatchesPerl #"[abc]+.+.?(a|b|c)"#
    , naiveMatchesPerl #"^[az.-]+$"#
    , naiveMatchesPerl #"^[a\-z\.]+$"#
    , naiveMatchesPerl #"^[^a-c-d]{,4}"#
    , naiveMatchesPerl #"..?[[:digit:]]"#
    , naiveMatchesPerl #".?.?[[:digit:]]"#
    , naiveMatchesPerl #".{,2}[[:digit:]]"#
    , naiveMatchesPerl #"^[^a-c-d]{,4}[[:digit:]]"#
    , naiveMatchesPerl #"^(?:[^a-c-d]{,4})?[[:digit:]]"#
    , naiveMatchesPerl #"^(?:(?:[^a-c-d]{,4})?[[:digit:]ab\x4F\x{004f}])+.*"#
    , naiveMatchesPerl #"^(?:(?:[^a-c-d]{,4})?[[:digit:]ab\x4F\x{004f}])+(?:.*)+"#
--    , naiveMatchesPerl #"^(?:(?:[^a-c-d]{,4})?[[:digit:]ab\x4F\x{004f}])+(?:.*)+fev\x4F\x{0000000000004F}+"#
    ]
  ]
