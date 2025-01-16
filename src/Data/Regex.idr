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

namespace Tuple

  -- Specialised version of `Data.List.Quantifiers.HList` since we can't match on it as on type
  public export
  data All : List Type -> Type where
    Nil : All []
    (::) : (x : a) -> All as -> All (a::as)

public export
0 (*) : Type -> Type -> Type
Unit * a = a
a * Unit = a
All as * All bs = All $ as ++ bs
All as * b = All $ as ++ [b]
a * All bs = All $ [a] ++ bs
a * b = All [a, b]

namespace Either

  -- Specialised version of `Data.List.Quantifiers.Any Prelude.id` since we can't match on it as on type
  -- extended with a flag of possible lack of a value
  public export
  data One : (canMiss : Bool) -> List Type -> Type where
    Nothing : One True as
    Here    : (x : a) -> One cm (a::as)
    There   : One False as -> One cm (a::as)

public export
0 (+) : Type -> Type -> Type
Unit + One cn bs = One True bs
One cm as + Unit = One True as
Unit + a = One True [a]
a + Unit = One True [a]
One cm as + One cn bs = One (cm || cn) (as ++ bs)
One cm as + b = One cm (as ++ [b])
a + One cm bs = One cm ([a] ++ bs)
a + b = One False [a, b]

export
data Regex : Type -> Type where
  Empty : Regex ()
  Sym   : (Char -> Bool) -> Regex Char
  Seq   : Regex a -> Regex b -> Regex $ a * b
  Sel   : Regex a -> Regex b -> Regex $ a + b
  Rep   : (mi, ma : Conat) -> Regex a -> Regex $ ColistNM mi ma a

x = Rep 4 5 (Sym (== 'a'))
y = x `Sel` Empty
