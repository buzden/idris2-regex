module Data.Regex

import public Data.Alternative
import Data.List
import Data.List.Quantifiers
import Data.List.Lazy
import public Data.List1
import public Data.Vect

import Syntax.IHateParens.List

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

  Rep       : Regex a -> Regex $ List a

  Bound     : (start : Bool) -> Regex ()
  Sym       : (Char -> Bool) -> Regex Char

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

--- Return the index after which the unmatched rest is
matchWhole' : Regex a -> (str : List Char) -> LazyList (Fin $ S str.length, a)
matchWhole' = go True where
  cutgo : forall a. Bool -> Regex b -> (str : List Char) -> (cut : Fin $ S str.length) -> (b -> a) -> LazyList (Fin $ S str.length, a)
  go : forall a. Bool -> Regex a -> (str : List Char) -> LazyList (Fin $ S str.length, a)
  go atStart (Map f r)      cs      = map @{Compose} f $ go atStart r cs
  go atStart (Seq [])       cs      = pure (FZ, [])
  go atStart (Seq $ r::rs)  cs      = go atStart r cs >>= \(idx, x) => cutgo (atStart && idx == FZ) (Seq rs) cs idx (x::)
  go atStart (Sel rs)       cs      = go atStart (assert_smaller rs $ pushOut !(lazyAllAnies rs)) cs
  go atStart (WithMatch rs) cs      = go atStart rs cs <&> \(idx, x) => (idx, take (finToNat idx) cs, x)
  go atStart rr@(Rep r)     cs      = case go atStart r cs of
                                        [] => pure (FZ, [])
                                        xs => xs >>= \case
                                          (FZ, x) => pure $ (FZ, [x])
                                          (idx@(FS _), x) => assert_total $ cutgo False rr cs idx (x::)
  go _       (Bound False)  []      = pure (FZ, ()) --           \--- we can assert that b/o `idx` is `FS`, so `ds < cs`
  go _       (Bound False)  cs      = empty
  go True    (Bound True)   cs      = pure (FZ, ())
  go False   (Bound True)   cs      = empty
  go _       (Sym _)        []      = empty
  go _       (Sym f)        (c::cs) = whenT (f c) (1, c)

  cutgo atStart r cs cut g = let (ds ** f) = precDrop cs cut in bimap f g <$> go atStart r ds

------------------------------
--- Additional combinators ---
------------------------------

export
oneOrMore : Regex a -> Regex $ List1 a
oneOrMore r = [| r ::: Rep r |]

export
repeatN : (n : Nat) -> Regex a -> Regex $ Vect n a
repeatN Z     _ = pure []
repeatN (S Z) r = r <&> pure
repeatN (S n) r = [| r :: repeatN n r |]

export
repeatAtLeast : (n : Nat) -> Regex a -> Regex $ List a
repeatAtLeast n r = [| map toList (repeatN n r) ++ Rep r |]

export
repeatAtMost : (m : Nat) -> Regex a -> Regex $ List a
repeatAtMost Z     _ = pure []
repeatAtMost (S m) r = [| r :: repeatAtMost m r |] <|> pure []

export
repeatNM : (n, m : Nat) -> (0 _ : n `LTE` m) => Regex a -> Regex $ List a
repeatNM n m r = [| map toList (repeatN n r) ++ repeatAtMost (m `minus` n) r |]

export
string : String -> Regex ()
string str = map (const ()) $ sequence $ unpack str <&> \k => Sym (== k)
