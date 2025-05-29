module Data.Regex

import public Data.Alternative
import Data.List
import public Data.List.Quantifiers
import public Data.List.Lazy
import public Data.List1
import Data.SnocList
import public Data.Vect

import public Syntax.IHateParens.List

%default total

----------------------------------------
--- The type and its implementations ---
----------------------------------------

export
data Regex : Type -> Type where
  Map       : (a -> b) -> Regex a -> Regex b

  Seq       : Lazy (All Regex tys) -> Regex $ All Prelude.id tys -- empty list always matches
  Sel       : Lazy (All Regex tys) -> Regex $ Any Prelude.id tys -- empty list never matches

  WithMatch : Regex a -> Regex (List Char, a)

  Rep1      : Regex a -> Regex $ List1 a

  Bound     : (start : Bool) -> Regex ()
  Sym       : (Char -> Bool) -> Regex Char

%name Regex r, rx

public export
Functor Regex where
  map f $ Map f' r = Map (f . f') r
  map f r          = Map f r

-- TODO to implement `Seq` fusion (looking inside `Map` and `WithMatch` too)
public export
Applicative Regex where
  pure x = Seq [] <&> const x
  x <*> y = Seq [x, y] <&> \[l, r] => l r

-- TODO to implement `Sel` fusion (looking inside `Map` and `WithMatch` too)
public export
Alternative Regex where
  empty = Sel [] <&> \case _ impossible
  x <|> y = Sel [x, y] <&> \case Here x => x; There (Here x) => x

-- TODO to be removed as soon as it's merged to the upstream
export
All (Show . p) xs => Show (Any p xs) where
  showPrec d @{s::ss} (Here x)  = showCon d "Here"  $ showArg x
  showPrec d @{s::ss} (There x) = showCon d "There" $ showArg x

export
[LowLevel] Show (Regex a) where
  showPrec d $ Map f r     = showCon d "Map" $ " <fun>" ++ showArg r
  showPrec d $ Seq rs      = showCon d "Seq" $ let _ = mapProperty (const $ assert_total LowLevel) rs in showArg rs
  showPrec d $ Sel rs      = showCon d "Sel" $ let _ = mapProperty (const $ assert_total LowLevel) rs in showArg rs
  showPrec d $ WithMatch r = showCon d "WithMatch" $ showArg r
  showPrec d $ Rep1 r      = showCon d "Rep1" $ showArg r
  showPrec d $ Bound start = showCon d "Bound" $ showArg start
  showPrec d $ Sym f       = showCon d "Sym" " <fun>"

-------------------
--- Interpreter ---
-------------------

precDrop : (xs : List a) -> (n : Fin $ S xs.length) -> (ys : List a ** Fin (S ys.length) -> Fin (S xs.length))
precDrop xs      FZ     = (xs ** id)
precDrop (x::xs) (FS i) = let (ys ** f) = precDrop xs i in (ys ** FS . f)

lazyAllAnies : All p xs -> LazyList (Any p xs)
lazyAllAnies [] = []
lazyAllAnies (x::xs) = Here x :: map There (lazyAllAnies xs)

pushOut : Functor p => Any (p . q) xs -> p $ Any q xs
pushOut @{fp} (Here v)  = map @{fp} Here v
pushOut @{fp} (There n) = map @{fp} There $ pushOut n

hasntMove : Maybe (Fin $ S n) -> Bool
hasntMove Nothing       = True
hasntMove (Just FZ)     = True
hasntMove (Just $ FS _) = False

filterNothings : LazyList (Maybe a, b) -> LazyList (Maybe a, b)
filterNothings xs = case filter (isJust . fst) xs of [] => xs; xs' => xs'

--- Return the index after which the unmatched rest is
export
rawMatch : Regex a -> (str : List Char) -> LazyList (Maybe $ Fin $ S str.length, a)
rawMatch = go True where
  go : forall a. Bool -> Regex a -> (str : List Char) -> LazyList (Maybe $ Fin $ S str.length, a)
  go atStart (Map f r)      cs      = map @{Compose} f $ go atStart r cs
  go atStart (Seq [])       cs      = pure (Nothing, [])
  go atStart (Seq $ r::rs)  cs      = filterNothings $ go atStart r cs >>= \(idx, x) => do
                                        let (ds ** f) = precDrop cs $ fromMaybe FZ idx
                                        let convIdx : Maybe (Fin $ S ds.length) -> Maybe (Fin $ S cs.length)
                                            convIdx $ Just i = Just $ f i
                                            convIdx Nothing  = idx $> f FZ
                                        filterNothings $ bimap convIdx (x::) <$> go (atStart && hasntMove idx) (Seq rs) ds
  go atStart (Sel rs)       cs      = filterNothings $ lazyAllAnies rs >>= \r => go atStart (assert_smaller rs $ pushOut r) cs
  go atStart (WithMatch rs) cs      = go atStart rs cs <&> \(idx, x) => (idx, maybe id (\i => take (finToNat i)) idx cs, x)
  go atStart rr@(Rep1 r)    cs      = filterNothings $ do
                                        (Just idx@(FS _), x) <- go atStart r cs | (idx, x) => pure (idx, singleton x)
                                        let (ds ** f) = precDrop cs idx -- can assert `ds < cs` because `idx` is `FS`
                                        case filter (isJust . fst) $ bimap (map f) ((x:::) . toList) <$> go False rr (assert_smaller cs ds) of
                                          [] => pure (Just idx, singleton x)
                                          xs => xs
  go _       (Bound False)  []      = pure (Just FZ, ())
  go _       (Bound False)  cs      = empty
  go True    (Bound True)   cs      = pure (Just FZ, ())
  go False   (Bound True)   cs      = empty
  go _       (Sym _)        []      = empty
  go _       (Sym f)        (c::cs) = whenT (f c) (Just 1, c)

export
matchWhole : Regex a -> String -> Maybe a
matchWhole r str = do
  (idx, x) <- head' $ rawMatch r $ unpack str
  guard (fromMaybe FZ idx /= last) $> x

lazySplits : List a -> LazyList (SnocList a, List a)
lazySplits []          = pure ([<], [])
lazySplits xxs@(x::xs) = ([<], xxs) :: (mapFst (:< x) <$> lazySplits xs)

export
rawMatchIn : Regex a -> List Char -> LazyList (List Char, List Char, a, List Char)
rawMatchIn r cs = lazySplits cs >>= \(pre, cs) => rawMatch r cs <&> \(idx, x) =>
  let (mid, post) = splitAt (finToNat $ fromMaybe FZ idx) cs in (asList pre, mid, x, post)

export
rawMatchAll : Regex a -> List Char -> LazyList (List (List Char, List Char, a), List Char)
rawMatchAll r cs = case rawMatchIn r cs of
  [] => pure ([], cs)
  xs => xs >>= \(pre, ms, mx, post) => if null pre then pure ([(pre, ms, mx)], post) else
    rawMatchAll r (assert_smaller cs post) <&> mapFst ((pre, ms, mx) ::)

public export
record OneMatchInside a where
  constructor MkOneMatchInside
  unmatchedPre  : String
  matchedStr    : String
  matchedVal    : a
  unmatchedPost : String

export
matchInside : Regex a -> String -> Maybe $ OneMatchInside a
matchInside r str = head' (rawMatchIn r $ unpack str) <&> \(pre, mid, x, post) => MkOneMatchInside (pack pre) (pack mid) x (pack post)

public export
data AllMatchedInside : Type -> Type where
  Stop  : (post : String) -> AllMatchedInside a
  Match : (pre : String) -> (matched : String) -> a -> (cont : AllMatchedInside a) -> AllMatchedInside a

public export
matchedCnt : AllMatchedInside a -> Nat
matchedCnt $ Stop {}         = Z
matchedCnt $ Match {cont, _} = S $ matchedCnt cont

export
matchAll : Regex a -> String -> AllMatchedInside a
matchAll r str = maybe (Stop str) (uncurry conv) $ head' $ rawMatchAll r $ unpack str where
  conv : List (List Char, List Char, a) -> (end : List Char) -> AllMatchedInside a
  conv stmids end = foldl (\ami, (pre, ms, mx) => Match (pack pre) (pack ms) mx ami) (Stop $ pack end) stmids

------------------------------
--- Additional combinators ---
------------------------------

export
rep : Regex a -> Regex $ List a
rep r = toList <$> Rep1 r <|> pure []

export %inline
rep1 : Regex a -> Regex $ List1 a
rep1 = Rep1

export
repeatN : (n : Nat) -> Regex a -> Regex $ Vect n a
repeatN Z     _ = pure []
repeatN (S Z) r = r <&> pure
repeatN (S n) r = [| r :: repeatN n r |]

export
repeatAtLeast : (n : Nat) -> Regex a -> Regex $ List a
repeatAtLeast n r = [| map toList (repeatN n r) ++ rep r |]

export
repeatAtMost : (m : Nat) -> Regex a -> Regex $ List a
repeatAtMost Z     _ = pure []
repeatAtMost (S m) r = [| r :: repeatAtMost m r |] <|> pure []

export
repeatNM : (n, m : Nat) -> (0 _ : n `LTE` m) => Regex a -> Regex $ List a
repeatNM n m r = [| map toList (repeatN n r) ++ repeatAtMost (m `minus` n) r |]

------------------------
--- Particular cases ---
------------------------

||| Always matches without consuming any symbol.
export %inline
omega : Regex ()
omega = pure ()

||| Matches a symbol satisfying the given predicate, and returns the matched char, or fails.
export %inline
sym : (Char -> Bool) -> Regex Char
sym = Sym

||| Matches the given symbol and returns it, or fails.
export %inline
char : Char -> Regex Char
char = sym . (==)

||| Matches the start of the line/text
export
sol : Regex ()
sol = Bound True

||| Matches the end of the line/text
export
eol : Regex ()
eol = Bound False

export %inline
withMatch : Regex a -> Regex (String, a)
withMatch = map (mapFst pack) . WithMatch

export %inline
matchedOf : Regex a -> Regex String
matchedOf = map fst . withMatch

export
string : String -> Regex String
string = map pack . sequence . map char . unpack

||| Matches all of given sub-regexes, sequentially.
export %inline
all : All Regex tys -> Regex $ HList tys
all = Seq . delay

||| Matches is there exists at least one sub-regex that matches.
export %inline
exists : All Regex tys -> Regex $ Any Prelude.id tys
exists = Sel . delay
