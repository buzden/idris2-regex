module Data.Regex

import Data.List.Quantifiers
import public Data.List1
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

public export
Applicative Regex where
  pure x = Empty <&> const x
  x <*> y = Seq [x, y] <&> \[l, r] => l r

public export
either : Regex a -> Regex b -> Regex $ Either a b
either x y = Sel [x, y] <&> \case Here x => Left x; There (Here x) => Right x

public export
or : Regex a -> Regex a -> Regex a
or x y = Sel [x, y] <&> \case Here x => x; There (Here x) => x

export
optional : Regex a -> Regex $ Maybe a
optional sub = Sel [sub, Empty] <&> \case Here x => Just x; There (Here ()) => Nothing

export
oneOrMore : Regex a -> Regex $ List1 a
oneOrMore r = Seq [r, Rep r] <&> \[x, xs] => x ::: xs

export
repeatN : (n : Nat) -> Regex a -> Regex $ Vect n a
repeatN Z     _ = pure []
repeatN (S Z) r = r <&> pure
repeatN (S n) r = [| r :: repeatN n r |]

export
repeatAtLeast : (n : Nat) -> Regex a -> Regex $ List a
repeatAtLeast n r = Seq [repeatN n r, Rep r] <&> \[ls, rs] => toList ls ++ rs

export
repeatAtMost : (m : Nat) -> Regex a -> Regex $ List a
repeatAtMost Z     _ = pure []
repeatAtMost (S m) r = [| r :: repeatAtMost m r |] `or` pure []

export
repeatNM : (n, m : Nat) -> (0 _ : n `LTE` m) => Regex a -> Regex $ List a
repeatNM n m r = Seq [repeatN n r, repeatAtMost (m `minus` n) r] <&> \[l, r] => toList l ++ r

export
string : String -> Regex ()
string str = map (const ()) $ sequence $ unpack str <&> \k => Sym (== k)
