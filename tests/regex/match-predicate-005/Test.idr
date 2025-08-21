module Test

import Text.Regex

LicPlateRX = all [ #"[ABEKMHOPCTYX]"#.erx, #"\d\d\d"#.erx, #"[ABEKMHOPCTYX][ABEKMHOPCTYX]"#.erx, #"\d\d\d?"#.erx ]
--LicPlateRX = #"ABEKMHOPCTYX]\d{3}[ABEKMHOPCTYX]{2}\d{2,3}"#.erx

record LicPlate where
  constructor MkLicPlate
  licPlate : String
  {auto 0 licPlateCorr : MatchesWhole LicPlateRX licPlate}

t : LicPlate
t = MkLicPlate "E127PO73"
