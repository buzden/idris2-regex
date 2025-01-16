module Data.Regex

import public Data.So

%default total

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

namespace ColistNM

  public export
  data ColistNM : (min, max : Conat) -> Type -> Type where
    Nil  : ColistNM Z ma a
    (::) : a -> ColistNM mi ma a -> mi' `LTE` S mi => S ma `LTE` ma' => ColistNM mi' ma' a

  xs : ColistNM 1 3 Nat
  xs = [1, 2, 3]

public export
0 (*) : Type -> Type -> Type
Unit * a = a
a * Unit = a
a * b = (a, b) -- TODO to use something like HList

public export
0 (+) : Type -> Type -> Type
Unit + a = Maybe a
a + Unit = Maybe a
a + b = Either a b -- TODO to use some speacial type for this

export
data Regex : Type -> Type where
  Empty : Regex ()
  Sym   : (Char -> Bool) -> Regex Char
  Seq   : Regex a -> Regex b -> Regex $ a * b
  Sel   : Regex a -> Regex b -> Regex $ a + b
  Rep   : (mi, ma : Conat) -> Regex a -> Regex $ ColistNM mi ma a

x = Rep 4 5 (Sym (== 'a'))
y = x `Sel` Empty
