||| Courtesy of @z-snails
module Core.Ord

import Core.CompileExpr
import Core.Name
import Core.TT
import Data.Vect

infixl 5 `thenCmp`

thenCmp : Ordering -> Lazy Ordering -> Ordering
thenCmp LT _ = LT
thenCmp EQ o = o
thenCmp GT _ = GT

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
        tag WorldVal = 13
        tag IntType = 14
        tag Int8Type = 15
        tag Int16Type = 16
        tag Int32Type = 17
        tag Int64Type = 18
        tag IntegerType = 19
        tag Bits8Type = 20
        tag Bits16Type = 21
        tag Bits32Type = 22
        tag Bits64Type = 23
        tag StringType = 24
        tag CharType = 25
        tag DoubleType = 26
        tag WorldType = 27


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


lrTag : LazyReason -> Int
lrTag LInf = 0
lrTag LLazy = 1
lrTag LUnknown = 2

export
Ord LazyReason where
    compare l1 l2 = compare (lrTag l1) (lrTag l2)

export
Eq (Var vars) where
    MkVar {i=i1} _ == MkVar {i=i2} _ = i1 == i2

export
Ord (Var vars) where
    MkVar {i=i1} _ `compare` MkVar {i=i2} _ = compare i1 i2

mutual
    export
    Eq (CExp vars) where
        CLocal {idx=x1} _ _ == CLocal {idx=x2} _ _ = x1 == x2
        CRef _ n1 == CRef _ n2 = n1 == n2
        CLam _ n1 e1 == CLam _ n2 e2 = case nameEq n1 n2 of
            Just Refl => e1 == e2
            Nothing => False
        CLet _ n1 _ val1 sc1 == CLet _ n2 _ val2 sc2 = case nameEq n1 n2 of
            Just Refl => val1 == val2 && sc1 == sc2
            Nothing => False
        CApp _ f1 a1 == CApp _ f2 a2 = f1 == f2 && a1 == a2
        CCon _ n1 _ t1 a1 == CCon _ n2 _ t2 a2 = t1 == t2 && n1 == n2 && a1 == a2
        COp _ f1 a1 == COp _ f2 a2 = case primFnEq f1 f2 of
            Just Refl => a1 == a2
            Nothing => False
        CExtPrim _ f1 a1 == CExtPrim _ f2 a2 = f1 == f2 && a1 == a2
        CForce _ l1 e1 == CForce _ l2 e2 = l1 == l2 && e1 == e2
        CDelay _ l1 e1 == CDelay _ l2 e2 = l1 == l2 && e1 == e2
        CConCase _ s1 a1 d1 == CConCase _ s2 a2 d2 = s1 == s2 && a1 == a2 && d1 == d2
        CConstCase _ s1 a1 d1 == CConstCase _ s2 a2 d2 = s1 == s2 && a1 == a2 && d1 == d2
        CPrimVal _ c1 == CPrimVal _ c2 = c1 == c2
        CErased _ == CErased _ = True
        CCrash _ m1 == CCrash _ m2 = m1 == m2
        _ == _ = False

    export
    Eq (CConAlt vars) where
        MkConAlt n1 _ t1 a1 e1 == MkConAlt n2 _ t2 a2 e2 = t1 == t2 && n1 == n2 && case namesEq a1 a2 of
            Just Refl => e1 == e2
            Nothing => False

    export
    Eq (CConstAlt vars) where
        MkConstAlt c1 e1 == MkConstAlt c2 e2 = c1 == c2 && e1 == e2

mutual
    export
    Ord (CExp vars) where
        CLocal {idx=x1} _ _ `compare` CLocal {idx=x2} _ _ = x1 `compare` x2
        CRef _ n1 `compare` CRef _ n2 = n1 `compare` n2
        CLam _ n1 e1 `compare` CLam _ n2 e2 = case nameEq n1 n2 of
            Just Refl => compare e1 e2
            Nothing => compare n1 n2
        CLet _ n1 _ val1 sc1 `compare` CLet _ n2 _ val2 sc2 = case nameEq n1 n2 of
            Just Refl => compare val1 val2 `thenCmp` compare sc1 sc2
            Nothing => compare n1 n2
        CApp _ f1 a1 `compare` CApp _ f2 a2 = compare f1 f2 `thenCmp` compare a1 a2
        CCon _ n1 _ t1 a1 `compare` CCon _ n2 _ t2 a2 = compare t1 t2 `thenCmp` compare n1 n2 `thenCmp` compare a1 a2
        COp _ f1 a1 `compare` COp _ f2 a2 = case primFnEq f1 f2 of
            Just Refl => compare a1 a2
            Nothing => primFnCmp f1 f2
        CExtPrim _ f1 a1 `compare` CExtPrim _ f2 a2 = compare f1 f2 `thenCmp` compare a1 a2
        CForce _ l1 e1 `compare` CForce _ l2 e2 = compare l1 l2 `thenCmp` compare e1 e2
        CDelay _ l1 e1 `compare` CDelay _ l2 e2 = compare l1 l2 `thenCmp` compare e1 e2
        CConCase _ s1 a1 d1 `compare` CConCase _ s2 a2 d2 = compare s1 s2 `thenCmp` compare a1 a2 `thenCmp` compare d1 d2
        CConstCase _ s1 a1 d1 `compare` CConstCase _ s2 a2 d2 = compare s1 s2 `thenCmp` compare a1 a2 `thenCmp` compare d1 d2
        CPrimVal _ c1 `compare` CPrimVal _ c2 = compare c1 c2
        CErased _ `compare` CErased _ = EQ
        CCrash _ m1 `compare` CCrash _ m2 = compare m1 m2
        e1 `compare` e2 = compare (tag e1) (tag e2)
          where
            tag : forall vars . CExp vars -> Int
            tag (CLocal _ _) = 0
            tag (CRef _ _) = 1
            tag (CLam _ _ _) = 2
            tag (CLet _ _ _ _ _) = 3
            tag (CApp _ _ _) = 4
            tag (CCon _ _ _ _ _) = 5
            tag (COp _ _ _) = 6
            tag (CExtPrim _ _ _) = 7
            tag (CForce _ _ _) = 8
            tag (CDelay _ _ _) = 9
            tag (CConCase _ _ _ _) = 10
            tag (CConstCase _ _ _ _) = 11
            tag (CPrimVal _ _) = 12
            tag (CErased _) = 13
            tag (CCrash _ _) = 14

    export
    Ord (CConAlt vars) where
        MkConAlt n1 _ t1 a1 e1 `compare` MkConAlt n2 _ t2 a2 e2 =
            compare t1 t2 `thenCmp` compare n1 n2 `thenCmp` case namesEq a1 a2 of
                Just Refl => compare e1 e2
                Nothing => compare a1 a2

    export
    Ord (CConstAlt vars) where
        MkConstAlt c1 e1 `compare` MkConstAlt c2 e2 = compare c1 c2 `thenCmp` compare e1 e2
