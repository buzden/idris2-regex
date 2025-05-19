module Data.Regex

import Data.List.Quantifiers
import public Data.So

%default total

namespace Conat

  public export
  data Conat : Type where
    Z : Conat
    S : Inf Conat -> Conat

  public export
  Infinity : Conat
  Infinity = S Infinity

  public export
  fromNat : Nat -> Conat
  fromNat Z     = Z
  fromNat $ S n = S $ fromNat n

  public export %inline
  fromInteger : (x : Integer) -> So (x >= 0) => Conat
  fromInteger x = fromNat $ fromInteger x

  public export
  data LTE : (l, r : Conat) -> Type where
    LTEZero : LTE Z m
    LTESucc : LTE n m -> LTE (S n) (S m)

  public export %defaulthint %inline
  ltezero : LTE Z m
  ltezero = LTEZero

namespace BoundedList

  public export
  data BoundedList : (min, max : Conat) -> Type -> Type where
    Nil  : BoundedList Z ma a
    (::) : a -> BoundedList mi ma a -> (0 _ : mi' `LTE` S mi) => (0 _ : S ma `LTE` ma') => BoundedList mi' ma' a

  xs : BoundedList 1 3 Nat
  xs = [1, 2, 3]

export
data Regex : Type -> Type where
  Empty : Regex ()
  Start : Regex ()
  End   : Regex ()
  Sym   : (Char -> Bool) -> Regex Char
  Seq   : All Regex tys -> Regex $ All Prelude.id tys
  Sel   : All Regex tys -> Regex $ Any Prelude.id tys
  Rep   : (mi, ma : Conat) -> (0 _ : mi `LTE` ma) => Regex a -> Regex $ BoundedList mi ma a

x = Rep 4 5 (Sym (== 'a'))
y = Sel [x, Empty]
