module Data.Regex

import public Data.Alternative
import Data.List
import public Data.List.Quantifiers
import public Data.List.Lazy
import public Data.List1
import Data.SnocList
import public Data.Vect

import public Syntax.IHateParens.List

import public Text.Regex.Interface

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

%name Regex.Regex r, rx

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
Alternative Regex.Regex where
  empty = Sel [] <&> \case _ impossible
  x <|> y = Sel [x, y] <&> \case Here x => x; There (Here x) => x

export
[LowLevel] Show (Regex.Regex a) where
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

---------------------------------------
--- Implementation of the interface ---
---------------------------------------

export
Regex Regex where
  rep1 = Rep1
  sym = Sym
  sol = Bound True
  eol = Bound False
  withMatch = map (mapFst pack) . WithMatch

export
RegexMatcher Regex where
  matchWhole r str = do
    (idx, x) <- head' $ rawMatch r $ unpack str
    guard (fromMaybe FZ idx /= last) $> x
  matchInside r str = head' (rawMatchIn r $ unpack str) <&> \(pre, mid, x, post) => MkOneMatchInside (pack pre) (pack mid) x (pack post)
  matchAll r str = maybe (Stop str) (uncurry conv) $ head' $ rawMatchAll r $ unpack str where
    conv : List (List Char, List Char, a) -> (end : List Char) -> AllMatchedInside a
    conv stmids end = foldl (\ami, (pre, ms, mx) => Match (pack pre) (pack ms) mx ami) (Stop $ pack end) stmids
