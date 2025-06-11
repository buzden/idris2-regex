module Text.Regex.Parser.ERE

import public Data.Either
import public Data.DPair

import public Language.Reflection

import public Text.Regex.Interface
import public Text.Regex.Parser

%default total

--------------
--- Lexing ---
--------------

data Chars
  = One Char
  | Class Bool CharClass -- False means negation of this char class
  | Range Char Char

data RxLex
  = C (SnocList Char)
  | WB Bool Bool -- word boundary, left, right, both or non-boundary
  | Cs Bool (List Chars) -- [...] and [^...], bool `False` for `[^...]`
  | Group Bool (SnocList RxLex) -- (...) and (?:...), bool `True` for matching group
  | SOL -- ^
  | EOL -- $
  | Alt -- |
  | AnyC -- .
  | Rep0 -- *
  | Rep1 -- +
  | Opt -- ?
  | RepN Nat -- {n}
  | RepN_ Nat -- {n,}
  | RepNM Nat Nat -- {n,m}
  | Rep_M Nat -- {,m}

data LexingContext : Type where
  E : SnocList RxLex -> LexingContext
  G : LexingContext -> (matching : Bool) -> (openingPos : Nat) -> SnocList RxLex -> LexingContext

push : LexingContext -> RxLex -> LexingContext
push (E $ ls :< C l)          (C r) = E $ ls :< C (l ++ r)
push (G sub m op $ ls :< C l) (C r) = G sub m op $ ls :< C (l ++ r)
push (E ls)          l = E $ ls :< l
push (G sub m op ls) l = G sub m op $ ls :< l

parseNat : (acc : Nat) -> (pos : Lazy Nat) -> List Char -> Either BadRegex Nat
parseNat acc pos [] = Left $ RegexIsBad pos "a number is expected"
parseNat acc pos (x::xs) = do
  let True = '0' <= x && x <= '9' | _ => Left $ RegexIsBad pos "bad number"
  let acc = acc * 10 + cast (ord x - ord '0')
  case xs of
    [] => pure acc
    _  => parseNat acc (S pos) xs

parseCharsSet : (startLen, origLen : Lazy Nat) -> (start : Bool) -> SnocList Chars -> List Char -> Either BadRegex (List Char, List Chars)
parseCharsSet stL orL start curr [] = Left $ RegexIsBad stL "unmatched opening bracket"
parseCharsSet stL orL False curr (']' :: xs) = pure (xs, cast curr)
parseCharsSet stL orL start curr lrxs@(l::'-'::r :: xs) = if l <= r
  then parseCharsSet stL orL False (curr :< Range l r) xs
  else Left $ RegexIsBad (orL `minus` length lrxs) "invalid range, left is greater than `right"
parseCharsSet stL orL start curr $ '\\'::'w' :: xs = parseCharsSet stL orL False (curr :< Class True  Word) xs
parseCharsSet stL orL start curr $ '\\'::'W' :: xs = parseCharsSet stL orL False (curr :< Class False Word) xs
parseCharsSet stL orL start curr $ '\\'::'s' :: xs = parseCharsSet stL orL False (curr :< Class True  Space) xs
parseCharsSet stL orL start curr $ '\\'::'S' :: xs = parseCharsSet stL orL False (curr :< Class False Space) xs
parseCharsSet stL orL start curr $ '\\'::'d' :: xs = parseCharsSet stL orL False (curr :< Class True  Digit) xs
parseCharsSet stL orL start curr $ '\\'::'D' :: xs = parseCharsSet stL orL False (curr :< Class False Digit) xs
parseCharsSet stL orL start curr $ '['::':'::'u'::'p'::'p'::'e'::'r'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Upper) xs
parseCharsSet stL orL start curr $ '['::':'::'l'::'o'::'w'::'e'::'r'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Lower) xs
parseCharsSet stL orL start curr $ '['::':'::'a'::'l'::'p'::'h'::'a'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Alpha) xs
parseCharsSet stL orL start curr $ '['::':'::'a'::'l'::'n'::'u'::'m'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Alnum) xs
parseCharsSet stL orL start curr $ '['::':'::'d'::'i'::'g'::'i'::'t'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Digit) xs
parseCharsSet stL orL start curr $ '['::':'::'x'::'d'::'i'::'g'::'i'::'t'::':'::']' :: xs = parseCharsSet stL orL False (curr :< Class True XDigit) xs
parseCharsSet stL orL start curr $ '['::':'::'p'::'u'::'n'::'c'::'t'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Punct) xs
parseCharsSet stL orL start curr $ '['::':'::'b'::'l'::'a'::'n'::'k'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Blank) xs
parseCharsSet stL orL start curr $ '['::':'::'s'::'p'::'a'::'c'::'e'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Space) xs
parseCharsSet stL orL start curr $ '['::':'::'c'::'n'::'t'::'r'::'l'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Cntrl) xs
parseCharsSet stL orL start curr $ '['::':'::'g'::'r'::'a'::'p'::'h'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Graph) xs
parseCharsSet stL orL start curr $ '['::':'::'p'::'r'::'i'::'n'::'t'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Print) xs
parseCharsSet stL orL start curr $ '['::':'::'a'::'s'::'c'::'i'::'i'::':'::']'      :: xs = parseCharsSet stL orL False (curr :< Class True Ascii) xs
parseCharsSet stL orL start curr $ '['::':'::'w'::'o'::'r'::'d'::':'::']'           :: xs = parseCharsSet stL orL False (curr :< Class True Word) xs
parseCharsSet stL orL start curr (x :: xs) = parseCharsSet stL orL False (curr :< One x) xs

lex : List Char -> Either BadRegex $ SnocList RxLex
lex orig = go (E [<]) orig where
  orL : Nat
  orL = length orig
  pos : (left : List Char) -> Nat
  pos xs = orL `minus` length xs
  go : LexingContext -> List Char -> Either BadRegex $ SnocList RxLex
  go (E curr)     [] = pure curr
  go (G _ _ op _) [] = Left $ RegexIsBad op "unmatched opening parenthesis"
  go ctx $ '.' :: xs = go (push ctx AnyC) xs
  go ctx $ '^' :: xs = go (push ctx SOL) xs
  go ctx $ '$' :: xs = go (push ctx EOL) xs
  go ctx $ '*' :: xs = go (push ctx Rep0) xs
  go ctx $ '+' :: xs = go (push ctx Rep1) xs
  go ctx $ '?' :: xs = go (push ctx Opt) xs
  go ctx $ '|' :: xs = go (push ctx Alt) xs
  go ctx xxs@('('::'?'::':' :: xs) = go (G ctx True  (pos xxs) [<]) xs
  go ctx xxs@('('::'?'      :: xs) = Left $ RegexIsBad (pos xs) "unknown type of special group"
  go ctx xxs@('('           :: xs) = go (G ctx False (pos xxs) [<]) xs
  go (E {}) xxs@(')' :: xs) = Left $ RegexIsBad (pos xxs) "unmatched closing parenthesis"
  go (G ctx mtch op ls) $ ')' :: xs = go (push ctx $ Group mtch ls) xs
  go ctx xxs@('['::'^' :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (push ctx $ Cs False cs) $ assert_smaller xs rest
  go ctx xxs@('['      :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (push ctx $ Cs True  cs) $ assert_smaller xs rest
  go ctx $ '{' :: xs = do let (bnds, rest) = span (/= '}') xs
                          let '}' :: rest = rest | _ => Left $ RegexIsBad (pos rest) "`}` is expected"
                          let pos : Lazy Nat := pos xs
                          let l@(_::_):::r@(_::_)::[] = split (== ',') bnds
                            | l:::[]     => parseNat Z pos l >>= \n => go (push ctx $ RepN n) $ assert_smaller xs rest
                            | []:::r::[] => parseNat Z pos r >>= \n => go (push ctx $ RepN_ n) $ assert_smaller xs rest
                            | l:::[]::[] => parseNat Z pos l >>= \n => go (push ctx $ Rep_M n) $ assert_smaller xs rest
                            | _          => Left $ RegexIsBad pos "too many commas in the bounds, zero or one is expected"
                          r <- parseNat Z (1 + pos + length l) r; l <- parseNat Z pos l
                          go (push ctx $ RepNM l r) $ assert_smaller xs rest
  go ctx $ '\\'::'w' :: xs = go (push ctx $ Cs True [Class True  Word]) xs
  go ctx $ '\\'::'W' :: xs = go (push ctx $ Cs True [Class False Word]) xs
  go ctx $ '\\'::'s' :: xs = go (push ctx $ Cs True [Class True  Space]) xs
  go ctx $ '\\'::'S' :: xs = go (push ctx $ Cs True [Class False Space]) xs
  go ctx $ '\\'::'d' :: xs = go (push ctx $ Cs True [Class True  Digit]) xs
  go ctx $ '\\'::'D' :: xs = go (push ctx $ Cs True [Class False Digit]) xs
  go ctx $ '\\'::'b' :: xs = go (push ctx $ WB True  True) xs
  go ctx $ '\\'::'B' :: xs = go (push ctx $ WB False False) xs
  go ctx $ '\\'::'<' :: xs = go (push ctx $ WB True  False) xs
  go ctx $ '\\'::'>' :: xs = go (push ctx $ WB False True) xs
  go ctx $ '\\'::'n'  :: xs = go (push ctx $ C [<'\n']) xs
  go ctx $ '\\'::'r'  :: xs = go (push ctx $ C [<'\r']) xs
  go ctx $ '\\'::'t'  :: xs = go (push ctx $ C [<'\t']) xs
  go ctx $ '\\'::'f'  :: xs = go (push ctx $ C [<'\f']) xs
  go ctx $ '\\'::'v'  :: xs = go (push ctx $ C [<'\v']) xs
  go ctx $ '\\'::'0'  :: xs = go (push ctx $ C [<'\0']) xs
  go ctx $ '\\'::'\\' :: xs = go (push ctx $ C [<'\\']) xs
  go ctx $ '\\'::xxs@(x::_) = Left $ RegexIsBad (pos xxs) "unknown quote character '\\\{show x}'"
  go ctx $ x :: xs = go (push ctx $ C [<x]) xs

---------------
--- Parsing ---
---------------

parseRegex' : Regex rx => SnocList RxLex -> Either BadRegex $ Exists $ \n => rx $ Vect n String

export %inline
parseRegex : Regex rx => String -> Either BadRegex $ Exists rx
parseRegex str = map (\(Evidence _ r) => Evidence _ r) . parseRegex' {rx} =<< lex (unpack str)

public export %inline
toRegex : Regex rx => (s : String) -> (0 _ : IsRight $ parseRegex {rx} s) => rx $ fst $ fromRight $ parseRegex {rx} s
toRegex s = snd $ fromRight $ parseRegex {rx} s

export %macro
(.erx) : Regex rx => String -> Elab $ rx a
(.erx) str = do
  let patchFC : Nat -> FC -> FC
      patchFC ofs fc@(MkFC origin (l, c) (l', _))        = if l /= l' then fc else let p = (l, c + cast ofs) in MkFC origin p p
      patchFC ofs fc@(MkVirtualFC origin (l, c) (l', _)) = if l /= l' then fc else let p = (l, c + cast ofs) in MkVirtualFC origin p p
      patchFC ofs EmptyFC                                = EmptyFC
  let Right $ Evidence ty r = parseRegex {rx} str
    | Left (RegexIsBad idx reason) => do failAt (patchFC idx $ getFC !(quote str)) "Bad regular expression at position \{show idx}: \{reason}"
  Just Refl <- catch $ check {expected = a = ty} `(Refl)
    | Nothing => do fail "Unable to match expected type \{show !(quote a)} with the regex type \{show !(quote ty)}"
  pure r
