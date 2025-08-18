module Test

import Text.Regex

EmailRX = all [ #"[\w\-\.]+@"#.erx, #"(?:[\w-]+\.)+"#.erx, #"[\w-]{2,}"#.erx ]

record Email where
  constructor MkEmail
  asStr : String
  {auto 0 emailCorr : MatchesWhole EmailRX asStr}

t : Email
t = MkEmail "test@example.com"
