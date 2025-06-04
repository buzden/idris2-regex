module Text.Matcher

import Data.Vect

%default total

---------------------------------------
--- Data types representing results ---
---------------------------------------

public export
record OneMatchInside a where
  constructor MkOneMatchInside
  unmatchedPre  : String
  matchedStr    : String
  matchedVal    : a
  unmatchedPost : String

public export
data AllMatchedInside : Type -> Type where
  Stop  : (post : String) -> AllMatchedInside a
  Match : (pre : String) -> (matched : String) -> (val : a) -> (cont : AllMatchedInside a) -> AllMatchedInside a

public export
matchedCnt : AllMatchedInside a -> Nat
matchedCnt $ Stop {}         = Z
matchedCnt $ Match {cont, _} = S $ matchedCnt cont

public export
matchesOnly' : (ms : AllMatchedInside a) -> Vect (matchedCnt ms) String
matchesOnly' $ Stop _                 = []
matchesOnly' $ Match _ matched _ cont = matched :: matchesOnly' cont

public export
matchesOnly : AllMatchedInside a -> List String
matchesOnly $ Stop _                 = []
matchesOnly $ Match _ matched _ cont = matched :: matchesOnly cont

-------------------------
--- Matcher interface ---
-------------------------

public export
interface TextMatcher tm where
  matchWhole  : tm a -> String -> Maybe a
  -- Invariant that must hold is that `unmatchedPre ++ matchedStr ++ unmatchedPost` must be equal to the original string
  matchInside : tm a -> String -> Maybe $ OneMatchInside a
  matchAll    : tm a -> String -> AllMatchedInside a

  matchWhole m str = matchInside m str >>= \case
    MkOneMatchInside "" _ val "" => Just val
    _                            => Nothing
  matchAll m str = do
    let Just $ MkOneMatchInside pre match val post = matchInside m str | Nothing => Stop str
    Match pre match val $ matchAll m $ assert_smaller str post
