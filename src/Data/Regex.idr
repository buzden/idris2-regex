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
  Map   : (a -> b) -> Regex a -> Regex b

  Seq   : Lazy (All Regex tys) -> Regex $ All Prelude.id tys -- empty list always matches
  Sel   : Lazy (All Regex tys) -> Regex $ Any Prelude.id tys -- empty list never matches

  Rep   : Regex a -> Regex $ List a

  Bound : (start : Bool) -> Regex ()
  Sym   : (Char -> Bool) -> Regex Char

public export
Functor Regex where
  map f $ Map f' r = Map (f . f') r
  map f r          = Map f r

-- TODO to implement `Seq` fusion (looking inside `Map` too)
public export
Applicative Regex where
  pure x = Seq [] <&> const x
  x <*> y = Seq [x, y] <&> \[l, r] => l r

-- TODO to implement `Sel` fusion (looking inside `Map` too)
public export
Alternative Regex where
  empty = Sel [] <&> \case _ impossible
  x <|> y = Sel [x, y] <&> \case Here x => x; There (Here x) => x

-------------------
--- Interpreter ---
-------------------

--- Return the index after which the unmatched rest is
matchWhole' : Regex a -> (str : List Char) -> LazyList (Fin $ S str.length, a)
matchWhole' = go True where
  go : forall a. Bool -> Regex a -> (str : List Char) -> LazyList (Fin $ S str.length, a)
  go atStart (Map f r)     cs      = map @{Compose} f $ go atStart r cs
  go atStart (Seq rs)      cs      = ?matches'_rhs_1
  go atStart (Sel rs)      cs      = ?matches_rhs_2
  go atStart rr@(Rep r)    cs      = go atStart r cs >>= \case (FZ, _) => []; (idx, x) => map (mapFst ?foo) $ go False rr $ assert_smaller cs $ drop (finToNat idx) cs
  go _       (Bound False) []      = pure (FZ, ())
  go _       (Bound False) cs      = empty
  go True    (Bound True)  cs      = pure (FZ, ())
  go False   (Bound True)  cs      = empty
  go _       (Sym _)       []      = empty
  go _       (Sym f)       (c::cs) = whenT (f c) (FZ, c)

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
