||| Parser of extended POSIX regular expressions with (hopefully) unambiguous extensions from PCRE.
module Text.Regex.Parser.ERE

import Data.Alternative
import Data.Bits
import public Data.Either
import public Data.DPair

import public Language.Reflection

import public Text.Regex.Interface
import public Text.Regex.Parser

%default total

--------------
--- Lexing ---
--------------

data NLType =
  ||| \N, i.e. [^\n\r]
  NonNL |
  ||| \R, i.e. (?:\x0d\x0a|\n|\r|\v)
  Generic |
  ||| \Z, i.e. (?:\R?\z)
  Final

data PostfixOp : Type where
  Rep0  : PostfixOp -- *
  Rep1  : PostfixOp -- +
  Opt   : PostfixOp -- ?
  RepN  : Nat -> PostfixOp -- {n}
  RepN_ : Nat -> PostfixOp -- {n,}
  RepNM : (l, r : Nat) -> (0 lr : l `LTE` r) => PostfixOp -- {n,m}
  Rep_M : Nat -> PostfixOp -- {,m}

data RxLex
  = C (SnocList Char)
  | WB Bool Bool -- word boundary, left, right, both or non-boundary
  | Cs Bool (List BracketChars) -- [...] and [^...], bool `False` for `[^...]`
  | Group Bool (SnocList RxLex) -- (...) and (?:...), bool `True` for matching group
  | Edge LineMode EdgeSide -- ^, $, \A, \z
  | NL NLType -- \N, \R, \Z
  | AnyC LineMode -- ., \X
  | Alt -- |
  | Post RxLex PostfixOp

postfixOp : Regex rx => PostfixOp -> rx a -> Exists rx
postfixOp Rep0         = Evidence _ . rep
postfixOp Rep1         = Evidence _ . rep1
postfixOp Opt          = Evidence _ . opt
postfixOp (RepN n)     = Evidence _ . repeatN n
postfixOp (RepN_ n)    = Evidence _ . repeatNOrMore n
postfixOp (RepNM n m)  = Evidence _ . repeatNM n m
postfixOp (Rep_M m)    = Evidence _ . repeatNOrLess m

data CtxtNesting : Type
record LexCtxt where
  constructor MkLexCtxt
  nesting : CtxtNesting
  lexemes : SnocList RxLex

data CtxtNesting : Type where
  E : CtxtNesting
  G : LexCtxt -> (matching : Bool) -> (openingPos : Nat) -> CtxtNesting

push : LexCtxt -> RxLex -> LexCtxt
push (MkLexCtxt ch $ ls :< C l) (C r) = MkLexCtxt ch $ ls :< C (l ++ r)
push (MkLexCtxt ch ls)          l     = MkLexCtxt ch $ ls :< l

pushPostfix : (pos : Lazy Nat) -> LexCtxt -> PostfixOp -> Either BadRegex LexCtxt
pushPostfix pos (MkLexCtxt ch $ sx :< C (cs@(_:<_) :< last)) op = pure $ MkLexCtxt ch $ sx :< C cs :< Post (C [<last]) op
pushPostfix pos (MkLexCtxt ch $ sx :< Alt                  ) _  = Left $ RegexIsBad pos "illegal postfix operator after `|`"
pushPostfix pos (MkLexCtxt ch $ sx :< Post {}              ) _  = Left $ RegexIsBad pos "illegal or unsupported double postfix operator"
pushPostfix pos (MkLexCtxt ch $ sx :< x                    ) op = pure $ MkLexCtxt ch $ sx :< Post x op
pushPostfix pos _                                            _  = Left $ RegexIsBad pos "nothing to apply the postfix operator"

lexERE : List Char -> Either BadRegex $ SnocList RxLex
lexERE orig = go (MkLexCtxt E [<]) orig where
  orL : Nat
  orL = length orig
  pos : (left : List Char) -> Nat
  pos xs = orL `minus` length xs
  go : LexCtxt -> List Char -> Either BadRegex $ SnocList RxLex
  go (MkLexCtxt E curr)       [] = pure curr
  go (MkLexCtxt (G _ _ op) _) [] = Left $ RegexIsBad op "unmatched opening parenthesis"
  go ctx $ '.' :: xs = go (push ctx $ AnyC Line) xs
  go ctx $ '^' :: xs = go (push ctx $ Edge Line Start) xs
  go ctx $ '$' :: xs = go (push ctx $ Edge Line End) xs
  go ctx $ '|' :: xs = go (push ctx Alt) xs
  go ctx xxs@('('::'?'::':' :: xs) = go (MkLexCtxt (G ctx False (pos xxs)) [<]) xs
  go ctx xxs@('('::'?'      :: xs) = Left $ RegexIsBad (pos xs) "unknown type of special group"
  go ctx xxs@('('           :: xs) = go (MkLexCtxt (G ctx True (pos xxs)) [<]) xs
  go (MkLexCtxt E _) xxs@(')' :: xs) = Left $ RegexIsBad (pos xxs) "unmatched closing parenthesis"
  go (MkLexCtxt (G ctx mtch op) ls) $ ')' :: xs = go (push ctx $ Group mtch ls) xs
  go ctx xxs@('['::'^' :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (push ctx $ Cs False cs) $ assert_smaller xs rest
  go ctx xxs@('['      :: xs) = parseCharsSet (pos xxs) orL True [<] xs >>= \(rest, cs) => go (push ctx $ Cs True  cs) $ assert_smaller xs rest
  go ctx xxs@('*' :: xs) = go !(pushPostfix (pos xxs) ctx Rep0) xs
  go ctx xxs@('+' :: xs) = go !(pushPostfix (pos xxs) ctx Rep1) xs
  go ctx xxs@('?' :: xs) = go !(pushPostfix (pos xxs) ctx Opt) xs
  go ctx xxs@('{' :: xs) = do let (bnds, rest) = span (/= '}') xs
                              let '}' :: rest = rest | _ => Left $ RegexIsBad (pos xxs) "unmatched opening curly bracket"
                              let posxs : Lazy Nat := pos xs
                              let l@(_::_):::r@(_::_)::[] = split (== ',') bnds
                                | l:::[]     => parseNat 10 posxs l >>= \n => go !(pushPostfix (pos xxs) ctx $ RepN n) $ assert_smaller xs rest
                                | []:::r::[] => parseNat 10 posxs r >>= \m => go !(pushPostfix (pos xxs) ctx $ Rep_M m) $ assert_smaller xs rest
                                | l:::[]::[] => parseNat 10 posxs l >>= \n => go !(pushPostfix (pos xxs) ctx $ RepN_ n) $ assert_smaller xs rest
                                | _          => Left $ RegexIsBad posxs "too many commas in the bounds, zero or one is expected"
                              r <- parseNat 10 (1 + posxs + length l) r; l <- parseNat 10 posxs l
                              let Yes lr = isLTE l r | No _ => Left $ RegexIsBad posxs "left bound must not be greater than right bound"
                              go !(pushPostfix (pos xxs) ctx $ RepNM l r) $ assert_smaller xs rest
  go ctx $ '\\'::'X' :: xs = go (push ctx $ AnyC Text) xs
  go ctx $ '\\'::'A' :: xs = go (push ctx $ Edge Text Start) xs
  go ctx $ '\\'::'z' :: xs = go (push ctx $ Edge Text End) xs
  go ctx $ '\\'::'Z' :: xs = go (push ctx $ NL Final) xs
  go ctx $ '\\'::'R' :: xs = go (push ctx $ NL Generic) xs
  go ctx $ '\\'::'N' :: xs = go (push ctx $ NL NonNL) xs
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
  go ctx $ '\\'::'n' :: xs = go (push ctx $ C [<'\n']) xs
  go ctx $ '\\'::'r' :: xs = go (push ctx $ C [<'\r']) xs
  go ctx $ '\\'::'t' :: xs = go (push ctx $ C [<'\t']) xs
  go ctx $ '\\'::'f' :: xs = go (push ctx $ C [<'\f']) xs
  go ctx $ '\\'::'v' :: xs = go (push ctx $ C [<'\v']) xs
  go ctx $ '\\'::'0' :: xs = go (push ctx $ C [<'\0']) xs
  go ctx $ '\\'::'a' :: xs = go (push ctx $ C [<'\a']) xs
  go ctx $ '\\'::'\\':: xs = go (push ctx $ C [<'\\']) xs
  go ctx $ '\\'::'x'::'{' :: xs = do
    let (hexes, rest) = span (/= '}') xs
    let '}' :: rest = rest | _ => Left $ RegexIsBad (pos xs `minus` 1) "unmatched opening curly bracket"
    n <- parseNat 16 (pos xs) hexes
    let True = shiftR (cast {to=Integer} n) 32 == 0 | False => Left $ RegexIsBad (pos xs) "we expect no more than a 32-bit hex number"
    go (push ctx $ C [< chr $ cast n]) $ assert_smaller xs rest
  go ctx $ '\\'::'x'::ulxs@(u::l :: xs) = parseNat 16 (pos ulxs) [u,l] >>= \n => go (push ctx $ C [< chr $ cast n]) xs
  go ctx xxs@('\\'::'x':: xs) = Left $ RegexIsBad (pos xxs) "bad hex character command, use formats \xFF or \x{FFF...}"
  go ctx $ '\\'::xxs@(x::_) = Left $ RegexIsBad (pos xxs) "unknown quote character '\\\{show x}'"
  go ctx $ x :: xs = go (push ctx $ C [<x]) xs

---------------
--- Parsing ---
---------------

crumple : Monoid a => {0 f : _} ->
          List (n ** f $ Vect n a) ->
          Exists $ \tys => (All f tys, (n ** (All Prelude.id tys -> Vect n a, Any Prelude.id tys -> Vect n a)))
crumple []                   = Evidence _ ([], MkDPair _ (\case [] => [], \case Here impossible))
crumple ((n ** r) :: rs) = do
  let Evidence tys' (rs, (n' ** (cAll, cAny))) = crumple {f} rs
  let spreadAny : Any Prelude.id (Vect n a :: tys') -> Vect (n + n') a
      spreadAny $ Here x  = x ++ replicate n' neutral
      spreadAny $ There x = replicate n neutral ++ cAny x
  Evidence _ (r::rs, (_ ** (\(x::xs) => x ++ cAll xs, spreadAny)))

concatAll : Regex rx => List (n ** rx $ Vect n String) -> (n ** rx $ Vect n String)
concatAll xs = let Evidence _ (rs, MkDPair _ (conv, _)) = crumple xs in (_ ** conv <$> all rs)

-- Operation priorities:
-- - highest: postfix ops: *, +, ?, {..}
-- - middle: sequencing
-- - low: infix op: |
parseRegex' : Regex rx => List RxLex -> Exists $ \n => rx $ Vect n String
parseRegex' @{rxi} = alts where
  alts : List RxLex -> Exists $ \n => rx $ Vect n String
  conseq : List RxLex -> List (n ** rx $ Vect n String)
  alts lxs = do
    let alts = forget $ concatAll . assert_total conseq <$> List.split (\case Alt => True; _ => False) lxs
    let Evidence tys (alts, (n ** (_, conv))) = crumple alts
    Evidence _ $ map conv $ exists alts
  conseq [] = pure (_ ** pure [])
  conseq $ C [<c]         :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ char c
  conseq $ C cs           :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ string (pack $ cast cs)
  conseq $ WB l r         :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ wordBoundary l r
  conseq $ Cs nonneg cs   :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ bracketMatcher nonneg cs
  conseq $ Group False sx :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ (alts $ cast sx).snd
  conseq $ Group True  sx :: xs = (:: conseq xs) $ MkDPair 1 $ (::[]) <$> matchOf (alts $ cast sx).snd
  conseq $ Edge t s       :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ edge t s
  conseq $ NL NonNL       :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ sym (not . isNL)
  conseq $ NL Generic     :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ genericNL
  conseq $ NL Final       :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ all [optional genericNL, edge Text End]
  conseq $ AnyC m         :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ anyChar m
  conseq $ Post lx op     :: xs = (:: conseq xs) $ MkDPair _ $ [] <$ (postfixOp op (alts [lx]).snd).snd
  conseq $ Alt            :: xs = (:: conseq xs) $ MkDPair _ $ pure [] -- should never happen, actually

export %inline
parseRegex : Regex rx => String -> Either BadRegex $ Exists rx
parseRegex str = (\(Evidence _ r) => Evidence _ r) . parseRegex' . cast <$> lexERE (unpack str)

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
    -- TODO to add nice error message when only count of matched groups is wrong
  pure r
