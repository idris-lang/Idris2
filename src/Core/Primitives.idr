module Core.Primitives

import Core.Context
import Core.TT
import Core.Name.ScopedList
import Core.Value
import Libraries.Utils.String

import Data.Vect

%default covering

public export
record Prim where
  constructor MkPrim
  {arity : Nat}
  fn : PrimFn arity
  type : ClosedTerm
  totality : Totality

binOp : (Constant -> Constant -> Maybe Constant) ->
        {vars : _} -> Vect 2 (NF vars) -> Maybe (NF vars)
binOp fn [NPrimVal fc x, NPrimVal _ y]
    = map (NPrimVal fc) (fn x y)
binOp _ _ = Nothing

unaryOp : (Constant -> Maybe Constant) ->
          {vars : _} -> Vect 1 (NF vars) -> Maybe (NF vars)
unaryOp fn [NPrimVal fc x]
    = map (NPrimVal fc) (fn x)
unaryOp _ _ = Nothing

castString : Vect 1 (NF vars) -> Maybe (NF vars)
castString [NPrimVal fc (I i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (I8 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (I16 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (I32 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (I64 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (BI i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (B8 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (B16 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (B32 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (B64 i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (Ch i)] = Just (NPrimVal fc (Str (stripQuotes (show i))))
castString [NPrimVal fc (Db i)] = Just (NPrimVal fc (Str (show i)))
castString _ = Nothing

castInteger : Vect 1 (NF vars) -> Maybe (NF vars)
castInteger [NPrimVal fc (I i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (I8 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (I16 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (I32 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (I64 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (B8 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (B16 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (B32 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (B64 i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (Ch i)] = Just (NPrimVal fc (BI (cast (cast {to=Int} i))))
castInteger [NPrimVal fc (Db i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (Str i)] = Just (NPrimVal fc (BI (cast i)))
castInteger _ = Nothing

castInt : Vect 1 (NF vars) -> Maybe (NF vars)
castInt [NPrimVal fc (I8 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (I16 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (I32 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (I64 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (BI i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (B8 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (B16 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (B32 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (B64 i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (Db i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (Ch i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (Str i)] = Just (NPrimVal fc (I (cast i)))
castInt _ = Nothing

constantIntegerValue : Constant -> Maybe Integer
constantIntegerValue (I i)   = Just $ cast i
constantIntegerValue (I8 i)   = Just $ cast i
constantIntegerValue (I16 i)   = Just $ cast i
constantIntegerValue (I32 i)   = Just $ cast i
constantIntegerValue (I64 i)   = Just $ cast i
constantIntegerValue (BI i)  = Just i
constantIntegerValue (B8 i)  = Just $ cast i
constantIntegerValue (B16 i) = Just $ cast i
constantIntegerValue (B32 i) = Just $ cast i
constantIntegerValue (B64 i) = Just $ cast i
constantIntegerValue _       = Nothing

castBits8 : Vect 1 (NF vars) -> Maybe (NF vars)
castBits8 [NPrimVal fc constant] =
    NPrimVal fc . B8 . cast <$> constantIntegerValue constant
castBits8 _ = Nothing

castBits16 : Vect 1 (NF vars) -> Maybe (NF vars)
castBits16 [NPrimVal fc constant] =
    NPrimVal fc . B16 . cast <$> constantIntegerValue constant
castBits16 _ = Nothing

castBits32 : Vect 1 (NF vars) -> Maybe (NF vars)
castBits32 [NPrimVal fc constant] =
    NPrimVal fc . B32 . cast <$> constantIntegerValue constant
castBits32 _ = Nothing

castBits64 : Vect 1 (NF vars) -> Maybe (NF vars)
castBits64 [NPrimVal fc constant] =
    NPrimVal fc . B64 . cast <$> constantIntegerValue constant
castBits64 _ = Nothing

castInt8 : Vect 1 (NF vars) -> Maybe (NF vars)
castInt8 [NPrimVal fc constant] =
    NPrimVal fc . I8 . cast <$> constantIntegerValue constant
castInt8 _ = Nothing

castInt16 : Vect 1 (NF vars) -> Maybe (NF vars)
castInt16 [NPrimVal fc constant] =
    NPrimVal fc . I16 . cast <$> constantIntegerValue constant
castInt16 _ = Nothing

castInt32 : Vect 1 (NF vars) -> Maybe (NF vars)
castInt32 [NPrimVal fc constant] =
    NPrimVal fc . I32 . cast <$> constantIntegerValue constant
castInt32 _ = Nothing

castInt64 : Vect 1 (NF vars) -> Maybe (NF vars)
castInt64 [NPrimVal fc constant] =
    NPrimVal fc . I64 . cast <$> constantIntegerValue constant
castInt64 _ = Nothing

castDouble : Vect 1 (NF vars) -> Maybe (NF vars)
castDouble [NPrimVal fc (I i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (I8 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (I16 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (I32 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (I64 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (B8 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (B16 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (B32 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (B64 i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (BI i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (Str i)] = Just (NPrimVal fc (Db (cast i)))
castDouble _ = Nothing

castChar : Vect 1 (NF vars) -> Maybe (NF vars)
castChar [NPrimVal fc (I i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (I8 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (I16 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (I32 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (I64 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (B8 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (B16 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (B32 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (B64 i)] = Just (NPrimVal fc (Ch (cast i)))
castChar [NPrimVal fc (BI i)] = Just (NPrimVal fc (Ch (cast i)))
castChar _ = Nothing

strLength : Vect 1 (NF vars) -> Maybe (NF vars)
strLength [NPrimVal fc (Str s)] = Just (NPrimVal fc (I (cast (length s))))
strLength _ = Nothing

strHead : Vect 1 (NF vars) -> Maybe (NF vars)
strHead [NPrimVal fc (Str "")] = Nothing
strHead [NPrimVal fc (Str str)]
    = Just (NPrimVal fc (Ch (assert_total (prim__strHead str))))
strHead _ = Nothing

strTail : Vect 1 (NF vars) -> Maybe (NF vars)
strTail [NPrimVal fc (Str "")] = Nothing
strTail [NPrimVal fc (Str str)]
    = Just (NPrimVal fc (Str (assert_total (prim__strTail str))))
strTail _ = Nothing

strIndex : Vect 2 (NF vars) -> Maybe (NF vars)
strIndex [NPrimVal fc (Str str), NPrimVal _ (I i)]
    = if i >= 0 && integerToNat (cast i) < length str
         then Just (NPrimVal fc (Ch (assert_total (prim__strIndex str i))))
         else Nothing
strIndex _ = Nothing

strCons : Vect 2 (NF vars) -> Maybe (NF vars)
strCons [NPrimVal fc (Ch x), NPrimVal _ (Str y)]
    = Just (NPrimVal fc (Str (strCons x y)))
strCons _ = Nothing

strAppend : Vect 2 (NF vars) -> Maybe (NF vars)
strAppend [NPrimVal fc (Str x), NPrimVal _ (Str y)]
    = Just (NPrimVal fc (Str (x ++ y)))
strAppend _ = Nothing

strReverse : Vect 1 (NF vars) -> Maybe (NF vars)
strReverse [NPrimVal fc (Str x)]
    = Just (NPrimVal fc (Str (reverse x)))
strReverse _ = Nothing

strSubstr : Vect 3 (NF vars) -> Maybe (NF vars)
strSubstr [NPrimVal fc (I start), NPrimVal _ (I len), NPrimVal _ (Str str)]
    = Just (NPrimVal fc (Str (prim__strSubstr start len str)))
strSubstr _ = Nothing


add : Constant -> Constant -> Maybe Constant
add (BI x) (BI y) = pure $ BI (x + y)
add (I x) (I y) = pure $ I (x + y)
add (I8 x) (I8 y) = pure $ I8 (x + y)
add (I16 x) (I16 y) = pure $ I16 (x + y)
add (I32 x) (I32 y) = pure $ I32 (x + y)
add (I64 x) (I64 y) = pure $ I64 (x + y)
add (B8 x) (B8 y) = pure $ B8 (x + y)
add (B16 x) (B16 y) = pure $ B16 (x + y)
add (B32 x) (B32 y) = pure $ B32 (x + y)
add (B64 x) (B64 y) = pure $ B64 (x + y)
add (Ch x) (Ch y) = pure $ Ch (cast (cast {to=Int} x + cast y))
add (Db x) (Db y) = pure $ Db (x + y)
add _ _ = Nothing

sub : Constant -> Constant -> Maybe Constant
sub (BI x) (BI y) = pure $ BI (x - y)
sub (I x) (I y) = pure $ I (x - y)
sub (I8 x) (I8 y) = pure $ I8 (x - y)
sub (I16 x) (I16 y) = pure $ I16 (x - y)
sub (I32 x) (I32 y) = pure $ I32 (x - y)
sub (I64 x) (I64 y) = pure $ I64 (x - y)
sub (B8 x) (B8 y) = pure $ B8 (x - y)
sub (B16 x) (B16 y) = pure $ B16 (x - y)
sub (B32 x) (B32 y) = pure $ B32 (x - y)
sub (B64 x) (B64 y) = pure $ B64 (x - y)
sub (Ch x) (Ch y) = pure $ Ch (cast (cast {to=Int} x - cast y))
sub (Db x) (Db y) = pure $ Db (x - y)
sub _ _ = Nothing

mul : Constant -> Constant -> Maybe Constant
mul (BI x) (BI y) = pure $ BI (x * y)
mul (B8 x) (B8 y) = pure $ B8 (x * y)
mul (B16 x) (B16 y) = pure $ B16 (x * y)
mul (B32 x) (B32 y) = pure $ B32 (x * y)
mul (B64 x) (B64 y) = pure $ B64 (x * y)
mul (I x) (I y) = pure $ I (x * y)
mul (I8 x) (I8 y) = pure $ I8 (x * y)
mul (I16 x) (I16 y) = pure $ I16 (x * y)
mul (I32 x) (I32 y) = pure $ I32 (x * y)
mul (I64 x) (I64 y) = pure $ I64 (x * y)
mul (Db x) (Db y) = pure $ Db (x * y)
mul _ _ = Nothing

div : Constant -> Constant -> Maybe Constant
div (BI x) (BI 0) = Nothing
div (BI x) (BI y) = pure $ BI (assert_total (x `div` y))
div (I x) (I 0) = Nothing
div (I x) (I y) = pure $ I (assert_total (x `div` y))
div (I8 x) (I8 0) = Nothing
div (I8 x) (I8 y) = pure $ I8 (assert_total (x `div` y))
div (I16 x) (I16 0) = Nothing
div (I16 x) (I16 y) = pure $ I16 (assert_total (x `div` y))
div (I32 x) (I32 0) = Nothing
div (I32 x) (I32 y) = pure $ I32 (assert_total (x `div` y))
div (I64 x) (I64 0) = Nothing
div (I64 x) (I64 y) = pure $ I64 (assert_total (x `div` y))
div (B8 x) (B8 0) = Nothing
div (B8 x) (B8 y) = pure $ B8 (assert_total (x `div` y))
div (B16 x) (B16 0) = Nothing
div (B16 x) (B16 y) = pure $ B16 (assert_total (x `div` y))
div (B32 x) (B32 0) = Nothing
div (B32 x) (B32 y) = pure $ B32 (assert_total (x `div` y))
div (B64 x) (B64 0) = Nothing
div (B64 x) (B64 y) = pure $ B64 (assert_total (x `div` y))
div (Db x) (Db y) = pure $ Db (x / y)
div _ _ = Nothing

mod : Constant -> Constant -> Maybe Constant
mod (BI x) (BI 0) = Nothing
mod (BI x) (BI y) = pure $ BI (assert_total (x `mod` y))
mod (I x) (I 0) = Nothing
mod (I x) (I y) = pure $ I (assert_total (x `mod` y))
mod (I8 x) (I8 0) = Nothing
mod (I8 x) (I8 y) = pure $ I8 (assert_total (x `mod` y))
mod (I16 x) (I16 0) = Nothing
mod (I16 x) (I16 y) = pure $ I16 (assert_total (x `mod` y))
mod (I32 x) (I32 0) = Nothing
mod (I32 x) (I32 y) = pure $ I32 (assert_total (x `mod` y))
mod (I64 x) (I64 0) = Nothing
mod (I64 x) (I64 y) = pure $ I64 (assert_total (x `mod` y))
mod (B8 x) (B8 0) = Nothing
mod (B8 x) (B8 y) = pure $ B8 (assert_total (x `mod` y))
mod (B16 x) (B16 0) = Nothing
mod (B16 x) (B16 y) = pure $ B16 (assert_total (x `mod` y))
mod (B32 x) (B32 0) = Nothing
mod (B32 x) (B32 y) = pure $ B32 (assert_total (x `mod` y))
mod (B64 x) (B64 0) = Nothing
mod (B64 x) (B64 y) = pure $ B64 (assert_total (x `mod` y))
mod _ _ = Nothing

shiftl : Constant -> Constant -> Maybe Constant
shiftl (I x) (I y) = pure $ I (prim__shl_Int x y)
shiftl (I8 x) (I8 y) = pure $ I8 (prim__shl_Int8 x y)
shiftl (I16 x) (I16 y) = pure $ I16 (prim__shl_Int16 x y)
shiftl (I32 x) (I32 y) = pure $ I32 (prim__shl_Int32 x y)
shiftl (I64 x) (I64 y) = pure $ I64 (prim__shl_Int64 x y)
shiftl (BI x) (BI y) = pure $ BI (prim__shl_Integer x y)
shiftl (B8 x) (B8 y) = pure $ B8 (prim__shl_Bits8 x y)
shiftl (B16 x) (B16 y) = pure $ B16 (prim__shl_Bits16 x y)
shiftl (B32 x) (B32 y) = pure $ B32 (prim__shl_Bits32 x y)
shiftl (B64 x) (B64 y) = pure $ B64 (prim__shl_Bits64 x y)
shiftl _ _ = Nothing

shiftr : Constant -> Constant -> Maybe Constant
shiftr (I x) (I y) = pure $ I (prim__shr_Int x y)
shiftr (I8 x) (I8 y) = pure $ I8 (prim__shr_Int8 x y)
shiftr (I16 x) (I16 y) = pure $ I16 (prim__shr_Int16 x y)
shiftr (I32 x) (I32 y) = pure $ I32 (prim__shr_Int32 x y)
shiftr (I64 x) (I64 y) = pure $ I64 (prim__shr_Int64 x y)
shiftr (BI x) (BI y) = pure $ BI (prim__shr_Integer x y)
shiftr (B8 x) (B8 y) = pure $ B8 $ (prim__shr_Bits8 x y)
shiftr (B16 x) (B16 y) = pure $ B16 (prim__shr_Bits16 x y)
shiftr (B32 x) (B32 y) = pure $ B32 (prim__shr_Bits32 x y)
shiftr (B64 x) (B64 y) = pure $ B64 (prim__shr_Bits64 x y)
shiftr _ _ = Nothing

band : Constant -> Constant -> Maybe Constant
band (I x) (I y) = pure $ I (prim__and_Int x y)
band (I8 x) (I8 y) = pure $ I8 (prim__and_Int8 x y)
band (I16 x) (I16 y) = pure $ I16 (prim__and_Int16 x y)
band (I32 x) (I32 y) = pure $ I32 (prim__and_Int32 x y)
band (I64 x) (I64 y) = pure $ I64 (prim__and_Int64 x y)
band (BI x) (BI y) = pure $ BI (prim__and_Integer x y)
band (B8 x) (B8 y) = pure $ B8 (prim__and_Bits8 x y)
band (B16 x) (B16 y) = pure $ B16 (prim__and_Bits16 x y)
band (B32 x) (B32 y) = pure $ B32 (prim__and_Bits32 x y)
band (B64 x) (B64 y) = pure $ B64 (prim__and_Bits64 x y)
band _ _ = Nothing

bor : Constant -> Constant -> Maybe Constant
bor (I x) (I y) = pure $ I (prim__or_Int x y)
bor (I8 x) (I8 y) = pure $ I8 (prim__or_Int8 x y)
bor (I16 x) (I16 y) = pure $ I16 (prim__or_Int16 x y)
bor (I32 x) (I32 y) = pure $ I32 (prim__or_Int32 x y)
bor (I64 x) (I64 y) = pure $ I64 (prim__or_Int64 x y)
bor (BI x) (BI y) = pure $ BI (prim__or_Integer x y)
bor (B8 x) (B8 y) = pure $ B8 (prim__or_Bits8 x y)
bor (B16 x) (B16 y) = pure $ B16 (prim__or_Bits16 x y)
bor (B32 x) (B32 y) = pure $ B32 (prim__or_Bits32 x y)
bor (B64 x) (B64 y) = pure $ B64 (prim__or_Bits64 x y)
bor _ _ = Nothing

bxor : Constant -> Constant -> Maybe Constant
bxor (I x) (I y) = pure $ I (prim__xor_Int x y)
bxor (B8 x) (B8 y) = pure $ B8 (prim__xor_Bits8 x y)
bxor (B16 x) (B16 y) = pure $ B16 (prim__xor_Bits16 x y)
bxor (B32 x) (B32 y) = pure $ B32 (prim__xor_Bits32 x y)
bxor (B64 x) (B64 y) = pure $ B64 (prim__xor_Bits64 x y)
bxor (I8 x) (I8 y) = pure $ I8 (prim__xor_Int8 x y)
bxor (I16 x) (I16 y) = pure $ I16 (prim__xor_Int16 x y)
bxor (I32 x) (I32 y) = pure $ I32 (prim__xor_Int32 x y)
bxor (I64 x) (I64 y) = pure $ I64 (prim__xor_Int64 x y)
bxor (BI x) (BI y) = pure $ BI (prim__xor_Integer x y)
bxor _ _ = Nothing

neg : Constant -> Maybe Constant
neg (BI x) = pure $ BI (-x)
neg (I x) = pure $ I (-x)
neg (I8 x) = pure $ I8 (-x)
neg (I16 x) = pure $ I16 (-x)
neg (I32 x) = pure $ I32 (-x)
neg (I64 x) = pure $ I64 (-x)
neg (B8 x) = pure $ B8 (-x)
neg (B16 x) = pure $ B16 (-x)
neg (B32 x) = pure $ B32 (-x)
neg (B64 x) = pure $ B64 (-x)
neg (Db x) = pure $ Db (-x)
neg _ = Nothing

toInt : Bool -> Constant
toInt True = I 1
toInt False = I 0

lt : Constant -> Constant -> Maybe Constant
lt (I x) (I y) = pure $ toInt (x < y)
lt (I8 x) (I8 y) = pure $ toInt (x < y)
lt (I16 x) (I16 y) = pure $ toInt (x < y)
lt (I32 x) (I32 y) = pure $ toInt (x < y)
lt (I64 x) (I64 y) = pure $ toInt (x < y)
lt (BI x) (BI y) = pure $ toInt (x < y)
lt (B8 x) (B8 y) = pure $ toInt (x < y)
lt (B16 x) (B16 y) = pure $ toInt (x < y)
lt (B32 x) (B32 y) = pure $ toInt (x < y)
lt (B64 x) (B64 y) = pure $ toInt (x < y)
lt (Str x) (Str y) = pure $ toInt (x < y)
lt (Ch x) (Ch y) = pure $ toInt (x < y)
lt (Db x) (Db y) = pure $ toInt (x < y)
lt _ _ = Nothing

lte : Constant -> Constant -> Maybe Constant
lte (I x) (I y) = pure $ toInt (x <= y)
lte (I8 x) (I8 y) = pure $ toInt (x <= y)
lte (I16 x) (I16 y) = pure $ toInt (x <= y)
lte (I32 x) (I32 y) = pure $ toInt (x <= y)
lte (I64 x) (I64 y) = pure $ toInt (x <= y)
lte (BI x) (BI y) = pure $ toInt (x <= y)
lte (B8 x) (B8 y) = pure $ toInt (x <= y)
lte (B16 x) (B16 y) = pure $ toInt (x <= y)
lte (B32 x) (B32 y) = pure $ toInt (x <= y)
lte (B64 x) (B64 y) = pure $ toInt (x <= y)
lte (Str x) (Str y) = pure $ toInt (x <= y)
lte (Ch x) (Ch y) = pure $ toInt (x <= y)
lte (Db x) (Db y) = pure $ toInt (x <= y)
lte _ _ = Nothing

eq : Constant -> Constant -> Maybe Constant
eq (I x) (I y) = pure $ toInt (x == y)
eq (I8 x) (I8 y) = pure $ toInt (x == y)
eq (I16 x) (I16 y) = pure $ toInt (x == y)
eq (I32 x) (I32 y) = pure $ toInt (x == y)
eq (I64 x) (I64 y) = pure $ toInt (x == y)
eq (BI x) (BI y) = pure $ toInt (x == y)
eq (B8 x) (B8 y) = pure $ toInt (x == y)
eq (B16 x) (B16 y) = pure $ toInt (x == y)
eq (B32 x) (B32 y) = pure $ toInt (x == y)
eq (B64 x) (B64 y) = pure $ toInt (x == y)
eq (Str x) (Str y) = pure $ toInt (x == y)
eq (Ch x) (Ch y) = pure $ toInt (x == y)
eq (Db x) (Db y) = pure $ toInt (x == y)
eq _ _ = Nothing

gte : Constant -> Constant -> Maybe Constant
gte (I x) (I y) = pure $ toInt (x >= y)
gte (I8 x) (I8 y) = pure $ toInt (x >= y)
gte (I16 x) (I16 y) = pure $ toInt (x >= y)
gte (I32 x) (I32 y) = pure $ toInt (x >= y)
gte (I64 x) (I64 y) = pure $ toInt (x >= y)
gte (BI x) (BI y) = pure $ toInt (x >= y)
gte (B8 x) (B8 y) = pure $ toInt (x >= y)
gte (B16 x) (B16 y) = pure $ toInt (x >= y)
gte (B32 x) (B32 y) = pure $ toInt (x >= y)
gte (B64 x) (B64 y) = pure $ toInt (x >= y)
gte (Str x) (Str y) = pure $ toInt (x >= y)
gte (Ch x) (Ch y) = pure $ toInt (x >= y)
gte (Db x) (Db y) = pure $ toInt (x >= y)
gte _ _ = Nothing

gt : Constant -> Constant -> Maybe Constant
gt (I x) (I y) = pure $ toInt (x > y)
gt (I8 x) (I8 y) = pure $ toInt (x > y)
gt (I16 x) (I16 y) = pure $ toInt (x > y)
gt (I32 x) (I32 y) = pure $ toInt (x > y)
gt (I64 x) (I64 y) = pure $ toInt (x > y)
gt (BI x) (BI y) = pure $ toInt (x > y)
gt (B8 x) (B8 y) = pure $ toInt (x > y)
gt (B16 x) (B16 y) = pure $ toInt (x > y)
gt (B32 x) (B32 y) = pure $ toInt (x > y)
gt (B64 x) (B64 y) = pure $ toInt (x > y)
gt (Str x) (Str y) = pure $ toInt (x > y)
gt (Ch x) (Ch y) = pure $ toInt (x > y)
gt (Db x) (Db y) = pure $ toInt (x > y)
gt _ _ = Nothing

doubleOp : (Double -> Double) -> Vect 1 (NF vars) -> Maybe (NF vars)
doubleOp f [NPrimVal fc (Db x)] = Just (NPrimVal fc (Db (f x)))
doubleOp f _ = Nothing

doubleExp : Vect 1 (NF vars) -> Maybe (NF vars)
doubleExp = doubleOp exp

doubleLog : Vect 1 (NF vars) -> Maybe (NF vars)
doubleLog = doubleOp log

doublePow : {vars : _ } -> Vect 2 (NF vars) -> Maybe (NF vars)
doublePow = binOp pow'
    where pow' : Constant -> Constant -> Maybe Constant
          pow' (Db x) (Db y) = pure $ Db (pow x y)
          pow' _ _ = Nothing

doubleSin : Vect 1 (NF vars) -> Maybe (NF vars)
doubleSin = doubleOp sin

doubleCos : Vect 1 (NF vars) -> Maybe (NF vars)
doubleCos = doubleOp cos

doubleTan : Vect 1 (NF vars) -> Maybe (NF vars)
doubleTan = doubleOp tan

doubleASin : Vect 1 (NF vars) -> Maybe (NF vars)
doubleASin = doubleOp asin

doubleACos : Vect 1 (NF vars) -> Maybe (NF vars)
doubleACos = doubleOp acos

doubleATan : Vect 1 (NF vars) -> Maybe (NF vars)
doubleATan = doubleOp atan

doubleSqrt : Vect 1 (NF vars) -> Maybe (NF vars)
doubleSqrt = doubleOp sqrt

doubleFloor : Vect 1 (NF vars) -> Maybe (NF vars)
doubleFloor = doubleOp floor

doubleCeiling : Vect 1 (NF vars) -> Maybe (NF vars)
doubleCeiling = doubleOp ceiling

-- Only reduce for concrete values
believeMe : Vect 3 (NF vars) -> Maybe (NF vars)
believeMe [_, _, val@(NDCon _ _ _ _ _)] = Just val
believeMe [_, _, val@(NTCon _ _ _ _ _)] = Just val
believeMe [_, _, val@(NPrimVal _ _)] = Just val
believeMe [_, _, NType fc u] = Just (NType fc u)
believeMe [_, _, val] = Nothing

primTyVal : PrimType -> ClosedTerm
primTyVal = PrimVal emptyFC . PrT

constTy : PrimType -> PrimType -> PrimType -> ClosedTerm
constTy a b c
    = let arr = fnType emptyFC in
    primTyVal a `arr` (primTyVal b `arr` primTyVal c)

constTy3 : PrimType -> PrimType -> PrimType -> PrimType -> ClosedTerm
constTy3 a b c d
    = let arr = fnType emptyFC in
    primTyVal a `arr`
         (primTyVal b `arr`
             (primTyVal c `arr` primTyVal d))

predTy : PrimType -> PrimType -> ClosedTerm
predTy a b = let arr = fnType emptyFC in
             primTyVal a `arr` primTyVal b

arithTy : PrimType -> ClosedTerm
arithTy t = constTy t t t

cmpTy : PrimType -> ClosedTerm
cmpTy t = constTy t t IntType

doubleTy : ClosedTerm
doubleTy = predTy DoubleType DoubleType

pi : (x : String) -> RigCount -> PiInfo (Term xs) -> Term xs ->
     Term (UN (Basic x) :%: xs) -> Term xs
pi x rig plic ty sc = Bind emptyFC (UN (Basic x)) (Pi emptyFC rig plic ty) sc

believeMeTy : ClosedTerm
believeMeTy
    = pi "a" erased Explicit (TType emptyFC (MN "top" 0)) $
      pi "b" erased Explicit (TType emptyFC (MN "top" 0)) $
      pi "x" linear Explicit (Local emptyFC Nothing _ (Later First)) $
      Local emptyFC Nothing _ (Later First)

crashTy : ClosedTerm
crashTy
    = pi "a" erased Explicit (TType emptyFC (MN "top" 0)) $
      pi "msg" top Explicit (PrimVal emptyFC $ PrT StringType) $
      Local emptyFC Nothing _ (Later First)

castTo : PrimType -> Vect 1 (NF vars) -> Maybe (NF vars)
castTo IntType = castInt
castTo Int8Type = castInt8
castTo Int16Type = castInt16
castTo Int32Type = castInt32
castTo Int64Type = castInt64
castTo IntegerType = castInteger
castTo Bits8Type = castBits8
castTo Bits16Type = castBits16
castTo Bits32Type = castBits32
castTo Bits64Type = castBits64
castTo StringType = castString
castTo CharType = castChar
castTo DoubleType = castDouble
castTo WorldType = const Nothing

export
getOp : {0 arity : Nat} -> PrimFn arity ->
        {vars : ScopedList Name} -> Vect arity (NF vars) -> Maybe (NF vars)
getOp (Add ty) = binOp add
getOp (Sub ty) = binOp sub
getOp (Mul ty) = binOp mul
getOp (Div ty) = binOp div
getOp (Mod ty) = binOp mod
getOp (Neg ty) = unaryOp neg
getOp (ShiftL ty) = binOp shiftl
getOp (ShiftR ty) = binOp shiftr

getOp (BAnd ty) = binOp band
getOp (BOr ty) = binOp bor
getOp (BXOr ty) = binOp bxor

getOp (LT ty) = binOp lt
getOp (LTE ty) = binOp lte
getOp (EQ ty) = binOp eq
getOp (GTE ty) = binOp gte
getOp (GT ty) = binOp gt

getOp StrLength = strLength
getOp StrHead = strHead
getOp StrTail = strTail
getOp StrIndex = strIndex
getOp StrCons = strCons
getOp StrAppend = strAppend
getOp StrReverse = strReverse
getOp StrSubstr = strSubstr

getOp DoubleExp = doubleExp
getOp DoubleLog = doubleLog
getOp DoublePow = doublePow
getOp DoubleSin = doubleSin
getOp DoubleCos = doubleCos
getOp DoubleTan = doubleTan
getOp DoubleASin = doubleASin
getOp DoubleACos = doubleACos
getOp DoubleATan = doubleATan
getOp DoubleSqrt = doubleSqrt
getOp DoubleFloor = doubleFloor
getOp DoubleCeiling = doubleCeiling

getOp (Cast _ y) = castTo y
getOp BelieveMe = believeMe

getOp _ = const Nothing

prim : String -> Name
prim str = UN $ Basic $ "prim__" ++ str

export
opName : {0 arity : Nat} -> PrimFn arity -> Name
opName (Add ty) = prim $ "add_" ++ show ty
opName (Sub ty) = prim $ "sub_" ++ show ty
opName (Mul ty) = prim $ "mul_" ++ show ty
opName (Div ty) = prim $ "div_" ++ show ty
opName (Mod ty) = prim $ "mod_" ++ show ty
opName (Neg ty) = prim $ "negate_" ++ show ty
opName (ShiftL ty) = prim $ "shl_" ++ show ty
opName (ShiftR ty) = prim $ "shr_" ++ show ty
opName (BAnd ty) = prim $ "and_" ++ show ty
opName (BOr ty) = prim $ "or_" ++ show ty
opName (BXOr ty) = prim $ "xor_" ++ show ty
opName (LT ty) = prim $ "lt_" ++ show ty
opName (LTE ty) = prim $ "lte_" ++ show ty
opName (EQ ty) = prim $ "eq_" ++ show ty
opName (GTE ty) = prim $ "gte_" ++ show ty
opName (GT ty) = prim $ "gt_" ++ show ty
opName StrLength = prim "strLength"
opName StrHead = prim "strHead"
opName StrTail = prim "strTail"
opName StrIndex = prim "strIndex"
opName StrCons = prim "strCons"
opName StrAppend = prim "strAppend"
opName StrReverse = prim "strReverse"
opName StrSubstr = prim "strSubstr"
opName DoubleExp = prim "doubleExp"
opName DoubleLog = prim "doubleLog"
opName DoublePow = prim "doublePow"
opName DoubleSin = prim "doubleSin"
opName DoubleCos = prim "doubleCos"
opName DoubleTan = prim "doubleTan"
opName DoubleASin = prim "doubleASin"
opName DoubleACos = prim "doubleACos"
opName DoubleATan = prim "doubleATan"
opName DoubleSqrt = prim "doubleSqrt"
opName DoubleFloor = prim "doubleFloor"
opName DoubleCeiling = prim "doubleCeiling"
opName (Cast x y) = prim $ "cast_" ++ show x ++ show y
opName BelieveMe = prim $ "believe_me"
opName Crash = prim $ "crash"

integralTypes : List PrimType
integralTypes = [ IntType
                , Int8Type
                , Int16Type
                , Int32Type
                , Int64Type
                , IntegerType
                , Bits8Type
                , Bits16Type
                , Bits32Type
                , Bits64Type
                ]

numTypes : List PrimType
numTypes = integralTypes ++ [DoubleType]

primTypes : List PrimType
primTypes = numTypes ++ [StringType, CharType]

export
allPrimitives : List Prim
allPrimitives =
    map (\t => MkPrim (Add t) (arithTy t) isTotal)     numTypes ++
    map (\t => MkPrim (Sub t) (arithTy t) isTotal)     numTypes ++
    map (\t => MkPrim (Mul t) (arithTy t) isTotal)     numTypes ++
    map (\t => MkPrim (Neg t) (predTy t t) isTotal)    numTypes ++
    map (\t => MkPrim (Div t) (arithTy t) notCovering) numTypes ++
    map (\t => MkPrim (Mod t) (arithTy t) notCovering) integralTypes ++

    map (\t => MkPrim (ShiftL t) (arithTy t) isTotal)  integralTypes ++
    map (\t => MkPrim (ShiftR t) (arithTy t) isTotal)  integralTypes ++
    map (\t => MkPrim (BAnd t) (arithTy t) isTotal)    integralTypes ++
    map (\t => MkPrim (BOr t) (arithTy t) isTotal)     integralTypes ++
    map (\t => MkPrim (BXOr t) (arithTy t) isTotal)    integralTypes ++

    map (\t => MkPrim (LT t) (cmpTy t) isTotal)  primTypes ++
    map (\t => MkPrim (LTE t) (cmpTy t) isTotal) primTypes ++
    map (\t => MkPrim (EQ t) (cmpTy t) isTotal)  primTypes ++
    map (\t => MkPrim (GTE t) (cmpTy t) isTotal) primTypes ++
    map (\t => MkPrim (GT t) (cmpTy t) isTotal)  primTypes ++

    [MkPrim StrLength (predTy StringType IntType) isTotal,
     MkPrim StrHead (predTy StringType CharType) notCovering,
     MkPrim StrTail (predTy StringType StringType) notCovering,
     MkPrim StrIndex (constTy StringType IntType CharType) notCovering,
     MkPrim StrCons (constTy CharType StringType StringType) isTotal,
     MkPrim StrAppend (arithTy StringType) isTotal,
     MkPrim StrReverse (predTy StringType StringType) isTotal,
     MkPrim StrSubstr (constTy3 IntType IntType StringType StringType) isTotal,
     MkPrim BelieveMe believeMeTy isTotal,
     MkPrim Crash crashTy notCovering] ++

    [MkPrim DoubleExp doubleTy isTotal,
     MkPrim DoubleLog doubleTy isTotal,
     MkPrim DoublePow (arithTy DoubleType) isTotal,
     MkPrim DoubleSin doubleTy isTotal,
     MkPrim DoubleCos doubleTy isTotal,
     MkPrim DoubleTan doubleTy isTotal,
     MkPrim DoubleASin doubleTy isTotal,
     MkPrim DoubleACos doubleTy isTotal,
     MkPrim DoubleATan doubleTy isTotal,
     MkPrim DoubleSqrt doubleTy isTotal,
     MkPrim DoubleFloor doubleTy isTotal,
     MkPrim DoubleCeiling doubleTy isTotal] ++

    -- support all combinations of primitive casts with the following
    -- exceptions: String -> Char, Double -> Char, Char -> Double
    [ MkPrim (Cast t1 t2) (predTy t1 t2) isTotal
    | t1 <- primTypes
    , t2 <- primTypes
    , t1 /= t2                         &&
      (t1,t2) /= (StringType,CharType) &&
      (t1,t2) /= (DoubleType,CharType) &&
      (t1,t2) /= (CharType,DoubleType)
    ]
