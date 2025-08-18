module Text.Matcher

import public Data.Maybe -- reexporting for `IsJust` in `MatchesWhole` and friends
import Data.SnocList
import Data.Vect

import Syntax.IHateParens.Function

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

public export %inline
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
matchedStrs' : (ms : AllMatchedInside a) -> Vect (matchedCnt ms) String
matchedStrs' $ Stop _                 = []
matchedStrs' $ Match _ matched _ cont = matched :: matchedStrs' cont

public export
matchedVals' : (ms : AllMatchedInside a) -> Vect (matchedCnt ms) a
matchedVals' $ Stop _             = []
matchedVals' $ Match _ _ val cont = val :: matchedVals' cont

public export
matchedStrs : AllMatchedInside a -> List String
matchedStrs $ Stop _                 = []
matchedStrs $ Match _ matched _ cont = matched :: matchedStrs cont

public export
matchedVals : AllMatchedInside a -> List a
matchedVals $ Stop _             = []
matchedVals $ Match _ _ val cont = val :: matchedVals cont

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

parameters {default False multiline : Bool}

  -- The following functions are a workaround of current inability of interfaces to hold functions with `default` arguments.
  public export %inline matchWhole  : TextMatcher tm => tm a -> String -> Maybe a                  ; matchWhole  = matchWhole' multiline
  public export %inline matchInside : TextMatcher tm => tm a -> String -> Maybe $ OneMatchInside a ; matchInside = matchInside' multiline
  public export %inline matchAll    : TextMatcher tm => tm a -> String -> AllMatchedInside a       ; matchAll    = matchAll' multiline

  -----------------------------
  --- Replacement functions ---
  -----------------------------

  export
  replaceOne : TextMatcher tm =>
               (pattern : tm a) ->
               (replacement : (match : String) -> (val : a) -> String) ->
               String -> String
  replaceOne pattern replacement str = maybe str rep $ matchInside pattern str where
    %inline rep : OneMatchInside a -> String
    rep $ MkOneMatchInside pre match val post = pre ++ replacement match val ++ post

  export
  replaceAll : TextMatcher tm =>
               (pattern : tm a) ->
               (replacement : (orig : String) -> (val : a) -> String) ->
               String -> String
  replaceAll pattern replacement = concat . rep [<] . matchAll pattern where
    rep : SnocList String -> AllMatchedInside a -> SnocList String
    rep acc $ Stop post                  = acc :< post
    rep acc $ Match pre matched val cont = rep .| acc :< pre :< replacement matched val .| cont

  public export %inline
  MatchesWhole : TextMatcher tm => tm a -> String -> Type
  MatchesWhole = IsJust .: matchWhole

  public export %inline
  MatchesInside : TextMatcher tm => tm a -> String -> Type
  MatchesInside = IsJust .: matchInside

--- Modifiers for replacement functions ---

public export %inline
(.str) : (t -> (String -> a -> String) -> String -> String) ->
         (t -> (String -> String)      -> String -> String)
f.str p r = f p $ const . r

public export %inline
(.val) : (t -> (String -> a -> String) -> String -> String) ->
         (t -> (a -> String)           -> String -> String)
f.val p = f p . const

public export %inline
(.const) : (t -> (String -> a -> String) -> String -> String) ->
           (t -> String                  -> String -> String)
f.const p = f p . const . const
