module Core.TT.Primitive

import Core.Name

import Data.String
import Data.Vect

import Decidable.Equality

import Idris.Pretty.Annotations

import Libraries.Data.Ordering.Extra
import Libraries.Data.Primitives
import Libraries.Data.String.Extra -- compatibility
import Libraries.Text.PrettyPrint.Prettyprinter

%default total

public export
data PrimType
    = IntType
    | Int8Type
    | Int16Type
    | Int32Type
    | Int64Type
    | IntegerType
    | Bits8Type
    | Bits16Type
    | Bits32Type
    | Bits64Type
    | StringType
    | CharType
    | DoubleType
    | WorldType

%name PrimType pty

public export
data Constant
    = I   Int
    | I8  Int8
    | I16 Int16
    | I32 Int32
    | I64 Int64
    | BI  Integer
    | B8  Bits8
    | B16 Bits16
    | B32 Bits32
    | B64 Bits64
    | Str String
    | Ch  Char
    | Db  Double
    | PrT PrimType
    | WorldVal

%name Constant cst

export
isConstantType : Name -> Maybe PrimType
isConstantType (UN (Basic n)) = case n of
  "Int"     => Just IntType
  "Int8"    => Just Int8Type
  "Int16"   => Just Int16Type
  "Int32"   => Just Int32Type
  "Int64"   => Just Int64Type
  "Integer" => Just IntegerType
  "Bits8"   => Just Bits8Type
  "Bits16"  => Just Bits16Type
  "Bits32"  => Just Bits32Type
  "Bits64"  => Just Bits64Type
  "String"  => Just StringType
  "Char"    => Just CharType
  "Double"  => Just DoubleType
  "%World"  => Just WorldType
  _ => Nothing
isConstantType _ = Nothing

export
isPrimType : Constant -> Bool
isPrimType (PrT _) = True
isPrimType _       = False

export
primTypeEq : (x, y : PrimType) -> Maybe (x = y)
primTypeEq IntType IntType = Just Refl
primTypeEq Int8Type Int8Type = Just Refl
primTypeEq Int16Type Int16Type = Just Refl
primTypeEq Int32Type Int32Type = Just Refl
primTypeEq Int64Type Int64Type = Just Refl
primTypeEq IntegerType IntegerType = Just Refl
primTypeEq StringType StringType = Just Refl
primTypeEq CharType CharType = Just Refl
primTypeEq DoubleType DoubleType = Just Refl
primTypeEq WorldType WorldType = Just Refl
primTypeEq _ _ = Nothing

-- TODO : The `TempXY` instances can be removed after the next release
--        (see also `Libraries.Data.Primitives`)
export
constantEq : (x, y : Constant) -> Maybe (x = y)
constantEq (I x) (I y) = case decEq x y of
                              Yes Refl => Just Refl
                              No contra => Nothing
constantEq (I8 x) (I8 y) = case decEq @{TempI8} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (I16 x) (I16 y) = case decEq @{TempI16} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (I32 x) (I32 y) = case decEq @{TempI32} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (I64 x) (I64 y) = case decEq @{TempI64} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B8 x) (B8 y) = case decEq @{TempB8} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B16 x) (B16 y) = case decEq @{TempB16} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B32 x) (B32 y) = case decEq @{TempB32} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B64 x) (B64 y) = case decEq @{TempB64} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (BI x) (BI y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Str x) (Str y) = case decEq x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (Ch x) (Ch y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Db x) (Db y) = Nothing -- no DecEq for Doubles!
constantEq (PrT x) (PrT y) = (\xy => cong PrT xy) <$> primTypeEq x y
constantEq WorldVal WorldVal = Just Refl

constantEq _ _ = Nothing

export
Show PrimType where
  show IntType = "Int"
  show Int8Type = "Int8"
  show Int16Type = "Int16"
  show Int32Type = "Int32"
  show Int64Type = "Int64"
  show IntegerType = "Integer"
  show Bits8Type = "Bits8"
  show Bits16Type = "Bits16"
  show Bits32Type = "Bits32"
  show Bits64Type = "Bits64"
  show StringType = "String"
  show CharType = "Char"
  show DoubleType = "Double"
  show WorldType = "%World"

export
Show Constant where
  show (I x) = show x
  show (I8 x) = show x
  show (I16 x) = show x
  show (I32 x) = show x
  show (I64 x) = show x
  show (BI x) = show x
  show (B8 x) = show x
  show (B16 x) = show x
  show (B32 x) = show x
  show (B64 x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show (PrT x) = show x
  show WorldVal = "%MkWorld"

Pretty IdrisSyntax PrimType where
  pretty c = annotate (TCon Nothing) $ case c of
    IntType => "Int"
    Int8Type => "Int8"
    Int16Type => "Int16"
    Int32Type => "Int32"
    Int64Type => "Int64"
    IntegerType => "Integer"
    Bits8Type => "Bits8"
    Bits16Type => "Bits16"
    Bits32Type => "Bits32"
    Bits64Type => "Bits64"
    StringType => "String"
    CharType => "Char"
    DoubleType => "Double"
    WorldType => "%World"

export
Pretty IdrisSyntax Constant where
  pretty (PrT x) = pretty x
  pretty v = annotate (DCon Nothing) $ pretty0 $ show v


export
Eq PrimType where
  IntType == IntType = True
  Int8Type == Int8Type = True
  Int16Type == Int16Type = True
  Int32Type == Int32Type = True
  Int64Type == Int64Type = True
  IntegerType == IntegerType = True
  Bits8Type == Bits8Type = True
  Bits16Type == Bits16Type = True
  Bits32Type == Bits32Type = True
  Bits64Type == Bits64Type = True
  StringType == StringType = True
  CharType == CharType = True
  DoubleType == DoubleType = True
  WorldType == WorldType = True
  _ == _ = False

export
Eq Constant where
  (I x) == (I y) = x == y
  (I8 x) == (I8 y) = x == y
  (I16 x) == (I16 y) = x == y
  (I32 x) == (I32 y) = x == y
  (I64 x) == (I64 y) = x == y
  (BI x) == (BI y) = x == y
  (B8 x) == (B8 y) = x == y
  (B16 x) == (B16 y) = x == y
  (B32 x) == (B32 y) = x == y
  (B64 x) == (B64 y) = x == y
  (Str x) == (Str y) = x == y
  (Ch x) == (Ch y) = x == y
  (Db x) == (Db y) = x == y
  (PrT x) == (PrT y) = x == y
  WorldVal == WorldVal = True
  _ == _ = False

export
Ord PrimType where
  compare = compare `on` tag
    where
      tag : PrimType -> Int
      tag IntType     = 1
      tag Int8Type    = 2
      tag Int16Type   = 3
      tag Int32Type   = 4
      tag Int64Type   = 5
      tag IntegerType = 6
      tag Bits8Type   = 7
      tag Bits16Type  = 8
      tag Bits32Type  = 9
      tag Bits64Type  = 10
      tag StringType  = 11
      tag CharType    = 12
      tag DoubleType  = 13
      tag WorldType   = 14

export
Ord Constant where
    I x `compare` I y = compare x y
    I8 x `compare` I8 y = compare x y
    I16 x `compare` I16 y = compare x y
    I32 x `compare` I32 y = compare x y
    I64 x `compare` I64 y = compare x y
    BI x `compare` BI y = compare x y
    B8 x `compare` B8 y = compare x y
    B16 x `compare` B16 y = compare x y
    B32 x `compare` B32 y = compare x y
    B64 x `compare` B64 y = compare x y
    Str x `compare` Str y = compare x y
    Ch x `compare` Ch y = compare x y
    Db x `compare` Db y = compare x y
    PrT x `compare` PrT y = compare x y
    compare x y = compare (tag x) (tag y)
      where
        tag : Constant -> Int
        tag (I _) = 0
        tag (I8 _) = 1
        tag (I16 _) = 2
        tag (I32 _) = 3
        tag (I64 _) = 4
        tag (BI _) = 5
        tag (B8 _) = 6
        tag (B16 _) = 7
        tag (B32 _) = 8
        tag (B64 _) = 9
        tag (Str _) = 10
        tag (Ch _) = 11
        tag (Db _) = 12
        tag (PrT _) = 13
        tag WorldVal = 14

-- for typecase
export
primTypeTag : PrimType -> Int
-- 1 = ->, 2 = Type
primTypeTag IntType = 3
primTypeTag IntegerType = 4
primTypeTag Bits8Type = 5
primTypeTag Bits16Type = 6
primTypeTag Bits32Type = 7
primTypeTag Bits64Type = 8
primTypeTag StringType = 9
primTypeTag CharType = 10
primTypeTag DoubleType = 11
primTypeTag WorldType = 12
primTypeTag Int8Type = 13
primTypeTag Int16Type = 14
primTypeTag Int32Type = 15
primTypeTag Int64Type = 16

||| Precision of integral types.
public export
data Precision = P Int | Unlimited

%name Precision prec

export
Eq Precision where
  (P m) == (P n)         = m == n
  Unlimited == Unlimited = True
  _         == _         = False

export
Ord Precision where
  compare (P m) (P n)         = compare m n
  compare Unlimited Unlimited = EQ
  compare Unlimited _         = GT
  compare _         Unlimited = LT

-- so far, we only support limited precision
-- unsigned integers
public export
data IntKind = Signed Precision | Unsigned Int

public export
intKind : PrimType -> Maybe IntKind
intKind IntegerType = Just $ Signed Unlimited
intKind Int8Type    = Just . Signed   $ P 8
intKind Int16Type   = Just . Signed   $ P 16
intKind Int32Type   = Just . Signed   $ P 32
intKind Int64Type   = Just . Signed   $ P 64
intKind IntType     = Just . Signed   $ P 64
intKind Bits8Type   = Just $ Unsigned 8
intKind Bits16Type  = Just $ Unsigned 16
intKind Bits32Type  = Just $ Unsigned 32
intKind Bits64Type  = Just $ Unsigned 64
intKind _           = Nothing

public export
precision : IntKind -> Precision
precision (Signed p)   = p
precision (Unsigned p) = P p

-- All the internal operators, parameterised by their arity
public export
data PrimFn : Nat -> Type where
     Add : (ty : PrimType) -> PrimFn 2
     Sub : (ty : PrimType) -> PrimFn 2
     Mul : (ty : PrimType) -> PrimFn 2
     Div : (ty : PrimType) -> PrimFn 2
     Mod : (ty : PrimType) -> PrimFn 2
     Neg : (ty : PrimType) -> PrimFn 1
     ShiftL : (ty : PrimType) -> PrimFn 2
     ShiftR : (ty : PrimType) -> PrimFn 2

     BAnd : (ty : PrimType) -> PrimFn 2
     BOr : (ty : PrimType) -> PrimFn 2
     BXOr : (ty : PrimType) -> PrimFn 2

     LT  : (ty : PrimType) -> PrimFn 2
     LTE : (ty : PrimType) -> PrimFn 2
     EQ  : (ty : PrimType) -> PrimFn 2
     GTE : (ty : PrimType) -> PrimFn 2
     GT  : (ty : PrimType) -> PrimFn 2

     StrLength : PrimFn 1
     StrHead : PrimFn 1
     StrTail : PrimFn 1
     StrIndex : PrimFn 2
     StrCons : PrimFn 2
     StrAppend : PrimFn 2
     StrReverse : PrimFn 1
     StrSubstr : PrimFn 3

     DoubleExp : PrimFn 1
     DoubleLog : PrimFn 1
     DoublePow : PrimFn 2
     DoubleSin : PrimFn 1
     DoubleCos : PrimFn 1
     DoubleTan : PrimFn 1
     DoubleASin : PrimFn 1
     DoubleACos : PrimFn 1
     DoubleATan : PrimFn 1
     DoubleSqrt : PrimFn 1
     DoubleFloor : PrimFn 1
     DoubleCeiling : PrimFn 1

     Cast : PrimType -> PrimType -> PrimFn 1
     BelieveMe : PrimFn 3
     Crash : PrimFn 2

%name PrimFn f

export
Show (PrimFn arity) where
  show (Add ty) = "+" ++ show ty
  show (Sub ty) = "-" ++ show ty
  show (Mul ty) = "*" ++ show ty
  show (Div ty) = "/" ++ show ty
  show (Mod ty) = "%" ++ show ty
  show (Neg ty) = "neg " ++ show ty
  show (ShiftL ty) = "shl " ++ show ty
  show (ShiftR ty) = "shr " ++ show ty
  show (BAnd ty) = "and " ++ show ty
  show (BOr ty) = "or " ++ show ty
  show (BXOr ty) = "xor " ++ show ty
  show (LT ty) = "<" ++ show ty
  show (LTE ty) = "<=" ++ show ty
  show (EQ ty) = "==" ++ show ty
  show (GTE ty) = ">=" ++ show ty
  show (GT ty) = ">" ++ show ty
  show StrLength = "op_strlen"
  show StrHead = "op_strhead"
  show StrTail = "op_strtail"
  show StrIndex = "op_strindex"
  show StrCons = "op_strcons"
  show StrAppend = "++"
  show StrReverse = "op_strrev"
  show StrSubstr = "op_strsubstr"
  show DoubleExp = "op_doubleExp"
  show DoubleLog = "op_doubleLog"
  show DoublePow = "op_doublePow"
  show DoubleSin = "op_doubleSin"
  show DoubleCos = "op_doubleCos"
  show DoubleTan = "op_doubleTan"
  show DoubleASin = "op_doubleASin"
  show DoubleACos = "op_doubleACos"
  show DoubleATan = "op_doubleATan"
  show DoubleSqrt = "op_doubleSqrt"
  show DoubleFloor = "op_doubleFloor"
  show DoubleCeiling = "op_doubleCeiling"
  show (Cast x y) = "cast-" ++ show x ++ "-" ++ show y
  show BelieveMe = "believe_me"
  show Crash = "crash"

export
prettyOp : PrimFn arity -> Vect arity (Doc IdrisSyntax) -> Doc IdrisSyntax
prettyOp op@(Add ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "+" <++> v2
prettyOp op@(Sub ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "-" <++> v2
prettyOp op@(Mul ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "*" <++> v2
prettyOp op@(Div ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`div`" <++> v2
prettyOp op@(Mod ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`mod`" <++> v2
prettyOp op@(Neg ty) [v] = annotate (Fun $ UN $ Basic $ show op) "-" <++> v
prettyOp op@(ShiftL ty) [v1,v2] = annotate (Fun $ UN $ Basic $ show op) "shiftl" <++> v1 <++> v2
prettyOp op@(ShiftR ty) [v1,v2] = annotate (Fun $ UN $ Basic $ show op) "shiftr" <++> v1 <++> v2
prettyOp op@(BAnd ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "&&" <++> v2
prettyOp op@(BOr ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "||" <++> v2
prettyOp op@(BXOr ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`xor`" <++> v2
prettyOp op@(LT ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "<" <++> v2
prettyOp op@(LTE ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "<=" <++> v2
prettyOp op@(EQ ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "==" <++> v2
prettyOp op@(GTE ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) ">=" <++> v2
prettyOp op@(GT ty) [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) ">" <++> v2
prettyOp op@StrLength [v] = annotate (Fun $ UN $ Basic $ show op) "length" <++> v
prettyOp op@StrHead [v] = annotate (Fun $ UN $ Basic $ show op) "head" <++> v
prettyOp op@StrTail [v] = annotate (Fun $ UN $ Basic $ show op) "tail" <++> v
prettyOp op@StrIndex [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "[" <+> v2 <+> annotate (Fun $ UN $ Basic $ show op) "]"
prettyOp op@StrCons [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "::" <++> v2
prettyOp op@StrAppend [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "++" <++> v2
prettyOp op@StrReverse [v] = annotate (Fun $ UN $ Basic $ show op) "reverse" <++> v
prettyOp op@StrSubstr [v1,v2,v3] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "[" <+> v2 <+> annotate (Fun $ UN $ Basic $ show op) "," <++> v3 <+> annotate (Fun $ UN $ Basic $ show op) "]"
prettyOp op@DoubleExp [v] = annotate (Fun $ UN $ Basic $ show op) "exp" <++> v
prettyOp op@DoubleLog [v] = annotate (Fun $ UN $ Basic $ show op) "log" <++> v
prettyOp op@DoublePow [v1,v2] = v1 <++> annotate (Fun $ UN $ Basic $ show op) "`pow`" <++> v2
prettyOp op@DoubleSin [v] = annotate (Fun $ UN $ Basic $ show op) "sin" <++> v
prettyOp op@DoubleCos [v] = annotate (Fun $ UN $ Basic $ show op) "cos" <++> v
prettyOp op@DoubleTan [v] = annotate (Fun $ UN $ Basic $ show op) "tan" <++> v
prettyOp op@DoubleASin [v] = annotate (Fun $ UN $ Basic $ show op) "asin" <++> v
prettyOp op@DoubleACos [v] = annotate (Fun $ UN $ Basic $ show op) "acos" <++> v
prettyOp op@DoubleATan [v] = annotate (Fun $ UN $ Basic $ show op) "atan" <++> v
prettyOp op@DoubleSqrt [v] = annotate (Fun $ UN $ Basic $ show op) "sqrt" <++> v
prettyOp op@DoubleFloor [v] = annotate (Fun $ UN $ Basic $ show op) "floor" <++> v
prettyOp op@DoubleCeiling [v] = annotate (Fun $ UN $ Basic $ show op) "ceiling" <++> v
prettyOp op@(Cast x y) [v] = annotate (Fun $ UN $ Basic $ show op) "[" <+> pretty x <++> annotate (Fun $ UN $ Basic $ show op) "->" <++> pretty y <+> annotate (Fun $ UN $ Basic $ show op) "]" <++> v
prettyOp op@BelieveMe [v1,v2,v3] = annotate (Fun $ UN $ Basic $ show op) "believe_me" <++> v1 <++> v2 <++> v3
prettyOp op@Crash [v1,v2] = annotate (Fun $ UN $ Basic $ show op) "crash" <++> v1 <++> v2

export
primFnEq : PrimFn a1 -> PrimFn a2 -> Maybe (a1 = a2)
primFnEq (Add t1) (Add t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (Sub t1) (Sub t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (Mul t1) (Mul t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (Div t1) (Div t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (Mod t1) (Mod t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (Neg t1) (Neg t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (ShiftL t1) (ShiftL t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (ShiftR t1) (ShiftR t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (BAnd t1) (BAnd t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (BOr t1) (BOr t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (BXOr t1) (BXOr t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (LT t1) (LT t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (LTE t1) (LTE t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (EQ t1) (EQ t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (GTE t1) (GTE t2) = if t1 == t2 then Just Refl else Nothing
primFnEq (GT t1) (GT t2) = if t1 == t2 then Just Refl else Nothing
primFnEq StrLength StrLength = Just Refl
primFnEq StrHead StrHead = Just Refl
primFnEq StrTail StrTail = Just Refl
primFnEq StrIndex StrIndex = Just Refl
primFnEq StrCons StrCons = Just Refl
primFnEq StrAppend StrAppend = Just Refl
primFnEq StrReverse StrReverse = Just Refl
primFnEq StrSubstr StrSubstr = Just Refl
primFnEq DoubleExp DoubleExp = Just Refl
primFnEq DoubleLog DoubleLog = Just Refl
primFnEq DoublePow DoublePow = Just Refl
primFnEq DoubleSin DoubleSin = Just Refl
primFnEq DoubleCos DoubleCos = Just Refl
primFnEq DoubleTan DoubleTan = Just Refl
primFnEq DoubleASin DoubleASin = Just Refl
primFnEq DoubleACos DoubleACos = Just Refl
primFnEq DoubleATan DoubleATan = Just Refl
primFnEq DoubleSqrt DoubleSqrt = Just Refl
primFnEq DoubleFloor DoubleFloor = Just Refl
primFnEq DoubleCeiling DoubleCeiling = Just Refl
primFnEq (Cast f1 t1) (Cast f2 t2) = if f1 == f2 && t1 == t2 then Just Refl else Nothing
primFnEq BelieveMe BelieveMe = Just Refl
primFnEq Crash Crash = Just Refl
primFnEq _ _ = Nothing

export
primFnCmp : PrimFn a1 -> PrimFn a2 -> Ordering
primFnCmp (Add t1) (Add t2) = compare t1 t2
primFnCmp (Sub t1) (Sub t2) = compare t1 t2
primFnCmp (Mul t1) (Mul t2) = compare t1 t2
primFnCmp (Div t1) (Div t2) = compare t1 t2
primFnCmp (Mod t1) (Mod t2) = compare t1 t2
primFnCmp (Neg t1) (Neg t2) = compare t1 t2
primFnCmp (ShiftL t1) (ShiftL t2) = compare t1 t2
primFnCmp (ShiftR t1) (ShiftR t2) = compare t1 t2
primFnCmp (BAnd t1) (BAnd t2) = compare t1 t2
primFnCmp (BOr t1) (BOr t2) = compare t1 t2
primFnCmp (BXOr t1) (BXOr t2) = compare t1 t2
primFnCmp (LT t1) (LT t2) = compare t1 t2
primFnCmp (LTE t1) (LTE t2) = compare t1 t2
primFnCmp (EQ t1) (EQ t2) = compare t1 t2
primFnCmp (GTE t1) (GTE t2) = compare t1 t2
primFnCmp (GT t1) (GT t2) = compare t1 t2
primFnCmp (Cast f1 t1) (Cast f2 t2) = compare f1 f2 `thenCmp` compare t1 t2
primFnCmp f1 f2 = compare (tag f1) (tag f2)
  where
    tag : forall ar. PrimFn ar -> Int
    tag (Add _) = 0
    tag (Sub _) = 1
    tag (Mul _) = 2
    tag (Div _) = 3
    tag (Mod _) = 4
    tag (Neg _) = 5
    tag (ShiftL _) = 6
    tag (ShiftR _) = 7
    tag (BAnd _) = 8
    tag (BOr _) = 9
    tag (BXOr _) = 10
    tag (LT _) = 11
    tag (LTE _) = 12
    tag (EQ _) = 13
    tag (GTE _) = 14
    tag (GT _) = 15
    tag StrLength = 16
    tag StrHead = 17
    tag StrTail = 18
    tag StrIndex = 19
    tag StrCons = 20
    tag StrAppend = 21
    tag StrReverse = 22
    tag StrSubstr = 23
    tag DoubleExp = 24
    tag DoubleLog = 25
    tag DoublePow = 26
    tag DoubleSin = 27
    tag DoubleCos = 28
    tag DoubleTan = 29
    tag DoubleASin = 30
    tag DoubleACos = 31
    tag DoubleATan = 32
    tag DoubleSqrt = 33
    tag DoubleFloor = 34
    tag DoubleCeiling = 35
    tag (Cast _ _) = 36
    tag BelieveMe = 37
    tag Crash = 38
