module Text.Regex.Naive

import public Data.Alternative
import Data.List
import public Data.List.Quantifiers
import public Data.List.Lazy
import public Data.List1
import Data.SnocList
import public Data.Vect

import public Syntax.IHateParens.List

import public Text.Regex.Interface
import public Text.Matcher

%default total

----------------------------------------
--- The type and its implementations ---
----------------------------------------

record RegExp (a : Type)

export
data RegExpOp : Type -> Type where
  Seq       : All RegExp tys -> RegExpOp $ All Prelude.id tys -- empty list always matches
  Sel       : All RegExp tys -> RegExpOp $ Any Prelude.id tys -- empty list never matches

  WordB     : (l, r : Bool) -> RegExpOp ()
  WithMatch : RegExp a -> RegExpOp (List Char, a)

  Rep1      : RegExp a -> RegExpOp $ List1 a

  Edge      : LineMode -> EdgeSide -> RegExpOp ()
  AnyChar   : LineMode -> RegExpOp Char
  Sym       : (Char -> Maybe a) -> RegExpOp a

export
record RegExp a where
  constructor RE
  operation : RegExpOp opTy
  mapping   : opTy -> a

%name RegExp r, rx

public export
Functor RegExp where
  map f = {mapping $= (f .)}

splitAt' : All f ls -> All g (ls ++ rs) -> (All g ls, All g rs)
splitAt' []      ps      = ([], ps)
splitAt' (_::xs) (p::ps) = mapFst (p::) (splitAt' xs ps)

public export
Applicative RegExp where
  pure x = Seq [] `RE` const x

  RE (Seq ls) ml <*> RE (Seq rs) mr = Seq (ls ++ rs) `RE` \xx => let (l, r) = splitAt' ls xx in ml l $ mr r
  RE (Seq ls) ml <*> r              = Seq (ls ++ [r]) `RE` \xx => let (l, r) = splitAt' ls xx in ml l $ head r
  l              <*> RE (Seq rs) mr = Seq (l :: rs) `RE` \(x::xs) => x $ mr xs
  l              <*> r              = Seq [l, r] `RE` \[l, r] => l r

altWith : All f ls -> (Any g ls -> a) -> (Any g rs -> a) -> Any g (ls ++ rs) -> a
altWith []      _ r an        = r an
altWith (x::xs) l r $ Here y  = l $ Here y
altWith (x::xs) l r $ There y = altWith xs (l . There) r y

theOnly : Any p [x] -> p x
theOnly $ Here y = y

public export
Alternative RegExp where
  empty = Sel [] `RE` \case _ impossible

  RE (Sel ls) ml <|> RE (Sel rs) mr = Sel (ls ++ rs) `RE` altWith ls ml mr
  l              <|> RE (Sel rs) mr = Sel (l :: rs) `RE` \case Here x => x; There y => mr y
  RE (Sel ls) ml <|> Delay r        = Sel (ls ++ [r]) `RE` altWith ls ml theOnly
  x              <|> y              = Sel [x, y] `RE` \case Here x => x; There (Here x) => x

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

postponeNothings : LazyList (Maybe a, b) -> LazyList (Maybe a, b)
postponeNothings xs = filter (isJust . fst) xs ++ filter (not . isJust . fst) xs

isText : LineMode -> Bool
isText Text = True
isText Line = False

--- Return the index after which the unmatched rest is
export
rawMatch : {default True beginning : Bool} -> (multiline : Bool) -> RegExp a -> (str : List Char) -> LazyList (Maybe $ Fin $ S str.length, a)
rawMatch multiline r orig = go' beginning r orig where
  prev : (curr : List Char) -> Maybe Char
  prev curr = do
    let origL = length orig
    let currL = length curr
    let True = origL > currL | False => Nothing
    let prevPos = origL `minus` S currL
    let Yes _ = inBounds prevPos orig | No _ => Nothing
    Just $ index prevPos orig
  go' : forall a. Bool -> RegExp a -> (str : List Char) -> LazyList (Maybe $ Fin $ S str.length, a)
  go : forall a. Bool -> RegExpOp a -> (str : List Char) -> LazyList (Maybe $ Fin $ S str.length, a)
  go' atStart (RE op ma) cs = map @{Compose} ma $ go atStart op cs
  go atStart (Seq [])          cs      = pure (Nothing, [])
  go atStart (Seq $ r::rs)     cs      = go' atStart r cs >>= \(idx, x) => do
                                           let (ds ** f) = precDrop cs $ fromMaybe FZ idx
                                           let convIdx : Maybe (Fin $ S ds.length) -> Maybe (Fin $ S cs.length)
                                               convIdx $ Just i = Just $ f i
                                               convIdx Nothing  = idx $> f FZ
                                           postponeNothings $ bimap convIdx (x::) <$> go (atStart && hasntMove idx) (Seq rs) ds
  go atStart (Sel rs)          cs      = postponeNothings $ lazyAllAnies rs >>= \r => go' atStart (assert_smaller rs $ pushOut r) cs
  go atStart (WordB l r)       cs      = do let wL = atStart || map (charClass Word) (prev cs) /= Just False
                                            let wR = map (charClass Word) (head' cs) /= Just False
                                            flip whenT (Just 0, ()) $ if l == r then l == (wL /= wR) else not wL == l && not wR == r
  go atStart (WithMatch rs)    cs      = go' atStart rs cs <&> \(idx, x) => (idx, maybe id (\i => take (finToNat i)) idx cs, x)
  go atStart rr@(Rep1 r)       cs      = do (Just idx@(FS _), x) <- go' atStart r cs | (idx, x) => pure (idx, singleton x)
                                            let (ds ** f) = precDrop cs idx -- can assert `ds < cs` because `idx` is `FS`
                                            let sub = filter (isJust . fst) $ bimap (map f) ((x:::) . toList) <$> go False rr (assert_smaller cs ds)
                                            sub ++ [(Just idx, singleton x)]
  go _       (Edge _    End)   []      = pure (Just FZ, ())
  go _       (Edge Line End)   (c::cs) = whenT (multiline && isNL c) (Just FZ, ())
  go _       (Edge Text End)   cs      = empty
  go True    (Edge _    Start) cs      = pure (Just FZ, ())
  go False   (Edge Line Start) cs      = whenTs multiline $ whenJs (prev cs) $ flip whenT (Just FZ, ()) . isNL
  go False   (Edge Text Start) cs      = empty
  go _       (AnyChar m)       []      = empty
  go _       (AnyChar m)       (c::cs) = whenT (not multiline || isText m || not (isNL c)) (Just 1, c)
  go _       (Sym _)           []      = empty
  go _       (Sym f)           (c::cs) = fromList $ toList $ (Just 1,) <$> f c

lazySplits : List a -> LazyList (SnocList a, List a)
lazySplits []          = pure ([<], [])
lazySplits xxs@(x::xs) = ([<], xxs) :: (mapFst (:< x) <$> lazySplits xs)

export
rawMatchIn : (multiline : Bool) -> RegExp a -> List Char -> LazyList (List Char, List Char, a, List Char)
rawMatchIn multiline r cs = lazySplits cs >>= \(pre, cs) => rawMatch {beginning=null pre} multiline r cs <&> \(idx, x) =>
  let (mid, post) = splitAt (finToNat $ fromMaybe FZ idx) cs in (asList pre, mid, x, post)

export
rawMatchAll : (multiline : Bool) -> RegExp a -> List Char -> LazyList (List (List Char, List Char, a), List Char)
rawMatchAll multiline r cs = case rawMatchIn multiline r cs of
  [] => pure ([], cs)
  xs => xs >>= \(pre, ms, mx, post) => if null pre then pure ([(pre, ms, mx)], post) else
    rawMatchAll multiline r (assert_smaller cs post) <&> mapFst ((pre, ms, mx) ::)

---------------------------------------
--- Implementation of the interface ---
---------------------------------------

namespace Regex

  export
  [Naive] Regex RegExp where
    sym'         = (`RE` id) . Sym
    anyChar      = (`RE` id) . AnyChar
    edge         = (`RE` id) .: Edge
    wordBoundary = (`RE` id) .: WordB
    withMatch    = (`RE` mapFst pack) . WithMatch
    all          = (`RE` id) . Seq
    exists       = (`RE` id) . Sel
    rep1         = (`RE` id) . Rep1

  public export %hint RegexRegExp : Regex RegExp; RegexRegExp = Naive

namespace Matcher

  export
  [Naive] TextMatcher RegExp where
    matchWhole' multiline r str = do
      (idx, x) <- head' $ rawMatch multiline r $ unpack str
      guard (fromMaybe FZ idx /= last) $> x
    matchInside' multiline r str =
      head' (rawMatchIn multiline r $ unpack str) <&> \(pre, mid, x, post) => MkOneMatchInside (pack pre) (pack mid) x (pack post)
    matchAll' multiline r str = maybe (Stop str) (uncurry conv) $ head' $ rawMatchAll multiline r $ unpack str where
      conv : List (List Char, List Char, a) -> (end : List Char) -> AllMatchedInside a
      conv stmids end = foldl (\ami, (pre, ms, mx) => Match (pack pre) (pack ms) mx ami) (Stop $ pack end) stmids

  public export %hint TextMatcherRegExp : TextMatcher RegExp; TextMatcherRegExp = Naive
