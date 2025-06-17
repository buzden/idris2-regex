module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Documentation" `atDir` "docs"
  , "Raw matcher"   `atDir` "raw-matcher"
  , "Lexer"         `atDir` "lexer"
  ]
