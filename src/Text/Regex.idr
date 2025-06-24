module Text.Regex

import public Text.Matcher
import public Text.Regex.Interface
import public Text.Regex.Naive
import public Text.Regex.Parser.ERE

%default total

public export %defaulthint
DefaultRegex : Regex RegExp
DefaultRegex = Naive

public export %defaulthint
DefaultTextMatcher : TextMatcher RegExp
DefaultTextMatcher = Naive
