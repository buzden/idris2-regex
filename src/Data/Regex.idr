module Data.Regex

import Data.List.Quantifiers
import public Data.List1
import public Data.Vect

%default total

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

export
optional : Regex a -> Regex $ Maybe a
optional sub = Just <$> sub <|> pure Nothing

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
