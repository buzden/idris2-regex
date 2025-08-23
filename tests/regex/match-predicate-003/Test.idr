module Test

import Text.Regex

EmailRX = #"[\w\-\.]+@(?:[\w-]+\.)+\w[\w-]+"#.erx

record Email where
  constructor MkEmail
  asStr : String
  {auto 0 emailCorr : MatchesWhole EmailRX asStr}

t : Email
t = MkEmail "test@example.com"
