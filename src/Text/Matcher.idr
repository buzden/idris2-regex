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

export
forgetVal : OneMatchInside a -> (String, String, String)
forgetVal $ MkOneMatchInside pre str _ post = (pre, str, post)

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
  matchWhole'  : (multiline : Bool) -> tm a -> String -> Maybe a
  -- Invariant that must hold is that `unmatchedPre ++ matchedStr ++ unmatchedPost` must be equal to the original string
  matchInside' : (multiline : Bool) -> tm a -> String -> Maybe $ OneMatchInside a
  matchAll'    : (multiline : Bool) -> tm a -> String -> AllMatchedInside a

  matchWhole' multiline m str = matchInside' multiline m str >>= \case
    MkOneMatchInside "" _ val "" => Just val
    _                            => Nothing
  matchAll' multiline m str = do
    let Just $ MkOneMatchInside pre match val post = matchInside' multiline m str | Nothing => Stop str
    if length post < length str
      then Match pre match val $ matchAll' multiline m $ assert_smaller str post
      else case strUncons str of
             Nothing => Match pre match val $ Stop post
             Just (k, str') => case matchAll' multiline m $ assert_smaller str str' of
               Stop post' => Match pre match val $ Stop $ strCons k post'
               Match pre' match' val' cont' => Match pre match val $ Match (strCons k pre') match' val' cont'

-- The following functions are a workaround of current inability of interfaces to hold functions with `default` arguments.

public export %inline
matchWhole  : {default False multiline : Bool} -> TextMatcher tm => tm a -> String -> Maybe a                  ; matchWhole  = matchWhole' multiline
public export %inline
matchInside : {default False multiline : Bool} -> TextMatcher tm => tm a -> String -> Maybe $ OneMatchInside a ; matchInside = matchInside' multiline
public export %inline
matchAll    : {default False multiline : Bool} -> TextMatcher tm => tm a -> String -> AllMatchedInside a       ; matchAll    = matchAll' multiline
