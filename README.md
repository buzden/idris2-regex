<!-- idris
module README

import Text.Regex
-->

# Regular expressions for Idris2

Rather simple library for working with regular expressions

## Structure

This library consists mainly of the following parts:

- `Regex` interface for building typed regular expressions (`Text.Regex.Interface`);
- Parsers for ERE (POSIX extended regular expressions) and globs, producing a value for any implementation of `Regex` interface
  (`Text.Regex.Parser.ERE` and `Text.Regex.Parser.Glob`);
- an ERE printer implementation for `Regex` interface (`Text.Regex.Printer`);
- `Matcher` interface for matching strings (`Text.Matcher`);
- a naive (not very effective) implementation for `Regex` and `Matcher` interfaces (`Text.Regex.Naive`).

When you import `Text.Regex`, you get both interfaces and ERE parser with the naive implementation being a default hint.

## Interface

TBD a table of what's supported.

## Parsing

TBD

- ERE parser supports POSIX extended regular expressions with some additions of Perl-compatible regular expressions; TODO a table.

- There are

  - a macro function for compile-time parsing of ERE called `.erx`;
  - pure functions for runtime-parsing (`parseRegex` and `parseGlob`, for ERE and glob respectively).

- Matching groups are parsed as a vector of appropriate matched strings.

- Glob parsers support file-style strings with support of `**` and non-dir semantics of `*`.

## Applying to strings

### Matching

We can do simple matching of a whole string in accordance to a regular expression:

<!-- idris
%unbound_implicits off
-->

```idris
e1 = matchWhole "ab(c|d)e".erx "abce" -- Just ["c"]
e2 = matchWhole "ab(c|d)e".erx "abcde" -- Nothing
```
<!-- idris
main_matchWhole : IO Unit
main_matchWhole = traverse_ printLn [e1, e2]
-->

You can also match a substring, one or all times:

```idris
e3 = matchInside "Idris( ?2)?".erx "Language Idris, also known as Idris 2"
e3_pre  = unmatchedPre  <$> e3 -- Just "Language "
e3_str  = matchedStr    <$> e3 -- Just "Idris"
e3_post = unmatchedPost <$> e3 -- Just ", also known as Idris 2"

e4 = matchedStrs $ matchAll "Idris( ?2)?".erx "Idris, also known as Idris 2"
     -- ["Idris", "Idris 2"]
```
<!-- idris
main_matchInside : IO Unit
main_matchInside = traverse_ printLn [e3_pre, e3_str, e3_post]
main_matchAll : IO Unit
main_matchAll = printLn e4
-->

You can also access matched value this way, e.g. the contents of the matching groups:

```idris
e5 = matchedVal <$> matchInside ".* (.*), *(.*)".erx "Language Idris, also known as Idris 2"
     -- Just ["Idris", "also known as Idris 2"]

```
<!-- idris
main_matchInside_with_match_groups : IO Unit
main_matchInside_with_match_groups = printLn e5
-->

### Replacing

One can use functions for replacing an internal match in a string: `replaceOne` and `replaceAll`.
Each function takes replacement function taking both matched value and matched string.
They have their variants where replacement function takes only string, value or nothing (constant).

```idris
r1 = replaceAll.const "a|b".erx "_" "mamma mia" -- "m_mm_ mi_"
r2 = replaceAll.const "m(a|b)".erx "_" "mamma mia" -- "_m_ mia"

r3 = replaceAll.str "m(?:a|b)".erx (\s => "[\{s}\{s}]") "mamma mia" -- "[mama]m[mama] mia"
r4 = replaceAll "m(.?)(?:a|b)".erx
       (\o, [i] => if null i then o else i ++ o ++ i) "mamma mia" -- "mammmam imiai"
r5 = replaceAll "m(.?)(a|b)".erx (\o, [i, r] => "[\{o}(\{i})<\{r}>]") "mamma mia"
     -- "[ma()<a>][mma(m)<a>] [mia(i)<a>]"
r6 = replaceAll.val "m(.?)(a|b)".erx
       (\[i, r] => if null i then "m" ++ r else i ++ r ++ i) "mamma mia" -- "mamam iai"
```
<!-- idris
main_replacements : IO Unit
main_replacements = traverse_ printLn [r1, r2, r3, r4, r5, r6]
-->

## Future

This library is still under construction.
There are a lot of things still wanted or missing, for example:

- type-level predicates for conforming a string to a regular expression;
- nice DSL for building regular expressions (e.g. using postfix functions);
- better efficiency of the naive implementation or alternative default implementation;
- support nested matching groups by the parser;
- support for extended features
  - lookaheads and lookbehinds;
  - greedy, reluctant and possessive quantifiers;
  - non-ASCII Unicode symbols in existing character classes;
  - named matching groups;
  - non-regular extensions, like back references to already matched groups;
  - comments syntax;
  - alternative syntaxes for char values, like `\u....` and octal ones;
- proper property-based tests for conformance to known mature implementations.
