module Data.Regex

import Data.List.Quantifiers
import public Data.Vect

%default total

export
data Regex : Type -> Type where
  Empty : Regex ()
  Map   : (a -> b) -> Regex a -> Regex b

  Bound : (start : Bool) -> Regex ()
  Sym   : (Char -> Bool) -> Regex Char
  Seq   : Lazy (All Regex tys) -> Regex $ All Prelude.id tys
  Sel   : Lazy (All Regex tys) -> Regex $ Any Prelude.id tys
  Rep   : Regex a -> Regex $ List a

public export
Functor Regex where
  map f $ Map f' r = Map (f . f') r
  map f r          = Map f r

export
optional : Regex a -> Regex $ Maybe a
optional sub = Sel [sub, Empty] <&> \case Here x => Just x; There (Here ()) => Nothing

export
repeatN : (n : Nat) -> Regex a -> Regex $ Vect n a
repeatN Z     _ = Empty <&> \() => []
repeatN (S Z) r = r <&> pure
repeatN (S n) r = Seq [r, repeatN n r] <&> \[x, xs] => x :: xs

export
repeatAtLeast : (n : Nat) -> Regex a -> Regex $ List a
repeatAtLeast n r = Seq [repeatN n r, Rep r] <&> \[ls, rs] => toList ls ++ rs

export
repeatAtMost : (m : Nat) -> Regex a -> Regex $ List a
repeatAtMost Z     _ = Empty <&> \() => []
repeatAtMost (S m) r = Sel [Seq [r, repeatAtMost m r] <&> \[x, xs] => x :: xs, Empty] <&> \case Here x => x; There (Here ()) => []

export
repeatNM : (n, m : Nat) -> (0 _ : n `LTE` m) => Regex a -> Regex $ List a
repeatNM n m r = Seq [repeatN n r, repeatAtMost (m `minus` n) r] <&> \[l, r] => toList l ++ r

export
sequentially : List (Regex a) -> Regex (List a)
sequentially xs = ?sequentially_rhs

export
string : String -> Regex ()
string str = map (const ()) $ sequentially $ unpack str <&> \k => Sym (== k)
