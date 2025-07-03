module Test

import Text.Regex

%default total

main : IO ()
main = Lazy.traverse_ putStrLn
  [ "\n--- replace `a` to `_`---\n"
  , replaceAll.const #"a|b"#.erx "_" "mama mia"

  , "\n--- replace `ma` or `m(a|b)` to `_`---\n"
  , replaceAll.const #"ma"#.erx "_" "mama mia"
  , replaceAll.const #"m(a|b)"#.erx "_" "mama mia"
  , replaceAll.str #"m(a|b)"#.erx (\s => "_") "mama mia"
  , replaceAll.str #"m(a|b)"#.erx (\s => s ++ s) "mama mia"

  , "\n--- replace `(m.?)(a|b)` with `\[x, y] => y ++ x ++ y` ---\n"
  , replaceAll.val #"(m.?)(a|b)"#.erx (\[x, y] => y ++ x ++ y) "mama mia"

  , "\n--- word bounds ---\n"
  , replaceAll.const #"\b"#.erx "_" "mama mia"
  , replaceAll.const #"\>"#.erx "_" "mama mia"
  , replaceAll.const #"\<"#.erx "_" "mama mia"
  , replaceAll.const #"\B"#.erx "_" "mama mia"

  , "\n--- replace all with empty match too---\n"
  , replaceAll "m(.?)(a|b)".erx (\o, [i, r] => "[\{o}(\{i})<\{r}>]") "mamma mia"
  ]
