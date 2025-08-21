module Test

import Text.Regex

UUID_RX = all [ "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]".erx
              , "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]-".erx
              , "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]-".erx
              , "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]-".erx
              , "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]-".erx
              , "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]".erx
              , "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]".erx
              , "[[:alnum:]][[:alnum:]]".erx, "[[:alnum:]][[:alnum:]]".erx
              ]
--UUID_RX = "[[:alnum:]]{8}-(?:[[:alnum:]]{4}-){3}[[:alnum:]]{12}".erx

record UUID where
  constructor MkUUID
  uuid : String
  {auto 0 uuidCorr : MatchesWhole UUID_RX uuid}

t : UUID
t = MkUUID "6a2f41a3-c54c-fce8-32d2-0324e1c32e22"
