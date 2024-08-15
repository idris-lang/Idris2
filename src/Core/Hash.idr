module Core.Hash

import Core.Case.CaseTree
import Core.CompileExpr
import Core.TT
import Core.Name.ScopedList

import Data.List1
import Libraries.Data.String.Iterator
import Data.Vect

%default covering

-- This is so that we can store a hash of the interface in ttc files, to avoid
-- the need for reloading modules when no interfaces have changed in imports.
-- As you can probably tell, I know almost nothing about writing good hash
-- functions, so better implementations will be very welcome...

public export
interface Hashable a where
  hash : a -> Int
  hashWithSalt : Int -> a -> Int

  hash = hashWithSalt 5381
  hashWithSalt h i = h * 33 + hash i

export infixl 5 `hashWithSalt`

export
Hashable Int where
  hash = id

export
Hashable Int8 where
  hash = cast

export
Hashable Int16 where
  hash = cast

export
Hashable Int32 where
  hash = cast

export
Hashable Int64 where
  hash = cast

export
Hashable Bits8 where
  hash = cast

export
Hashable Bits16 where
  hash = cast

export
Hashable Bits32 where
  hash = cast

export
Hashable Bits64 where
  hash = cast

export
Hashable Integer where
  hash = fromInteger

export
Hashable Nat where
  hash = cast

export
Hashable Char where
  hash = cast

export
Hashable a => Hashable (Vect n a) where
  hashWithSalt h [] = abs h
  hashWithSalt h (x :: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable a => Hashable (List a) where
  hashWithSalt h [] = abs h
  hashWithSalt h (x :: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable a => Hashable (ScopedList a) where
  hashWithSalt h [<] = abs h
  hashWithSalt h (x :%: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable a => Hashable (List1 a) where
  hashWithSalt h xxs = hashWithSalt (h * 33 + hash (head xxs)) (tail xxs)

export
Hashable a => Hashable (Maybe a) where
  hashWithSalt h Nothing = abs h
  hashWithSalt h (Just x) = hashWithSalt h x

export
Hashable a => Hashable b => Hashable (a, b) where
  hashWithSalt h (x, y) = h `hashWithSalt` x `hashWithSalt` y

export
Hashable String where
  hashWithSalt h = String.Iterator.foldl hashWithSalt h

export
Hashable Double where
  hash = hash . show

export
Hashable Namespace where
  hashWithSalt h ns = hashWithSalt h (unsafeUnfoldNamespace ns)

export
Hashable Name where
  hashWithSalt h (MN s _) = hashWithSalt h s
  hashWithSalt h (DN _ n) = hashWithSalt h n
  hashWithSalt h (NS ns n) = hashWithSalt (hashWithSalt h ns) n
  hashWithSalt h (Resolved i) = hashWithSalt h i
  hashWithSalt h n = hashWithSalt h (show n)

export
Hashable RigCount where
  hashWithSalt h = elimSemi
                     (hashWithSalt h 0)
                     (hashWithSalt h 1)
                     (const $ hashWithSalt h 2)

export
Hashable t => Hashable (PiInfo t) where
  hashWithSalt h Implicit = hashWithSalt h 0
  hashWithSalt h Explicit = hashWithSalt h 1
  hashWithSalt h AutoImplicit = hashWithSalt h 2
  hashWithSalt h (DefImplicit t) = h `hashWithSalt` 3 `hashWithSalt` t

export
Hashable ty => Hashable (Binder ty) where
  hashWithSalt h (Lam _ c p ty)
      = h `hashWithSalt` 0 `hashWithSalt` c `hashWithSalt` p `hashWithSalt` ty
  hashWithSalt h (Let _ c val ty)
      = h `hashWithSalt` 1 `hashWithSalt` c `hashWithSalt` val `hashWithSalt` ty
  hashWithSalt h (Pi _ c p ty)
      = h `hashWithSalt` 2 `hashWithSalt` c `hashWithSalt` p `hashWithSalt` ty
  hashWithSalt h (PVar _ c p ty)
      = h `hashWithSalt` 3 `hashWithSalt` c `hashWithSalt` p `hashWithSalt` ty
  hashWithSalt h (PLet _ c val ty)
      = h `hashWithSalt` 4 `hashWithSalt` c `hashWithSalt` val `hashWithSalt` ty
  hashWithSalt h (PVTy _ c ty)
      = h `hashWithSalt` 5 `hashWithSalt` c `hashWithSalt` ty

Hashable (Var vars) where
  hashWithSalt h (MkVar {varIdx = i} _) = hashWithSalt h i

mutual
  export
  Hashable (Term vars) where
    hashWithSalt h (Local fc x idx y)
        = h `hashWithSalt` 0 `hashWithSalt` idx
    hashWithSalt h (Ref fc x name)
        = h `hashWithSalt` 1 `hashWithSalt` name
    hashWithSalt h (Meta fc x y xs)
        = h `hashWithSalt` 2 `hashWithSalt` y `hashWithSalt` xs
    hashWithSalt h (Bind fc x b scope)
        = h `hashWithSalt` 3 `hashWithSalt` b `hashWithSalt` scope
    hashWithSalt h (App fc fn arg)
        = h `hashWithSalt` 4 `hashWithSalt` fn `hashWithSalt` arg
    hashWithSalt h (As fc _ nm pat)
        = h `hashWithSalt` 5 `hashWithSalt` nm `hashWithSalt` pat
    hashWithSalt h (TDelayed fc x y)
        = h `hashWithSalt` 6 `hashWithSalt` y
    hashWithSalt h (TDelay fc x t y)
        = h `hashWithSalt` 7 `hashWithSalt` t `hashWithSalt` y
    hashWithSalt h (TForce fc r x)
        = h `hashWithSalt` 8 `hashWithSalt` x
    hashWithSalt h (PrimVal fc c)
        = h `hashWithSalt` 9 `hashWithSalt` (show c)
    hashWithSalt h (Erased fc _)
        = hashWithSalt h 10
    hashWithSalt h (TType fc u)
        = hashWithSalt h 11 `hashWithSalt` u

  export
  Hashable Pat where
    hashWithSalt h (PAs fc nm pat)
        = h `hashWithSalt` 0 `hashWithSalt` nm `hashWithSalt` pat
    hashWithSalt h (PCon fc x tag arity xs)
        = h `hashWithSalt` 1 `hashWithSalt` x `hashWithSalt` xs
    hashWithSalt h (PTyCon fc x arity xs)
        = h `hashWithSalt` 2 `hashWithSalt` x `hashWithSalt` xs
    hashWithSalt h (PConst fc c)
        = h `hashWithSalt` 3 `hashWithSalt` (show c)
    hashWithSalt h (PArrow fc x s t)
        = h `hashWithSalt` 4 `hashWithSalt` s `hashWithSalt` t
    hashWithSalt h (PDelay fc r t p)
        = h `hashWithSalt` 5 `hashWithSalt` t `hashWithSalt` p
    hashWithSalt h (PLoc fc x)
        = h `hashWithSalt` 6 `hashWithSalt` x
    hashWithSalt h (PUnmatchable fc x)
        = h `hashWithSalt` 7 `hashWithSalt` x

  export
  Hashable (CaseTree vars) where
    hashWithSalt h (Case idx x scTy xs)
        = h `hashWithSalt` 0 `hashWithSalt` idx `hashWithSalt` xs
    hashWithSalt h (STerm _ x)
        = h `hashWithSalt` 1 `hashWithSalt` x
    hashWithSalt h (Unmatched msg)
        = h `hashWithSalt` 2
    hashWithSalt h Impossible
        = h `hashWithSalt` 3

  export
  Hashable (CaseAlt vars) where
    hashWithSalt h (ConCase x tag args y)
        = h `hashWithSalt` 0 `hashWithSalt` x `hashWithSalt` args
            `hashWithSalt` y
    hashWithSalt h (DelayCase t x y)
        = h `hashWithSalt` 2 `hashWithSalt` (show t)
            `hashWithSalt` (show x) `hashWithSalt` y
    hashWithSalt h (ConstCase x y)
        = h `hashWithSalt` 3 `hashWithSalt` (show x) `hashWithSalt` y
    hashWithSalt h (DefaultCase x)
        = h `hashWithSalt` 4 `hashWithSalt` x

export
Hashable CFType where
  hashWithSalt h = \case
    CFUnit =>
      h `hashWithSalt` 0
    CFInt =>
      h `hashWithSalt` 1
    CFUnsigned8 =>
      h `hashWithSalt` 2
    CFUnsigned16 =>
      h `hashWithSalt` 3
    CFUnsigned32 =>
      h `hashWithSalt` 4
    CFUnsigned64 =>
      h `hashWithSalt` 5
    CFString =>
      h `hashWithSalt` 6
    CFDouble =>
      h `hashWithSalt` 7
    CFChar =>
      h `hashWithSalt` 8
    CFPtr =>
      h `hashWithSalt` 9
    CFGCPtr =>
      h `hashWithSalt` 10
    CFBuffer =>
      h `hashWithSalt` 11
    CFWorld =>
      h `hashWithSalt` 12
    CFFun a b =>
      h `hashWithSalt` 13 `hashWithSalt` a `hashWithSalt` b
    CFIORes a =>
      h `hashWithSalt` 14 `hashWithSalt` a
    CFStruct n fs =>
      h `hashWithSalt` 15 `hashWithSalt` n `hashWithSalt` fs
    CFUser n xs =>
      h `hashWithSalt` 16 `hashWithSalt` n `hashWithSalt` xs
    CFInt8 =>
      h `hashWithSalt` 17
    CFInt16 =>
      h `hashWithSalt` 18
    CFInt32 =>
      h `hashWithSalt` 19
    CFInt64 =>
      h `hashWithSalt` 20
    CFForeignObj =>
      h `hashWithSalt` 21
    CFInteger =>
      h `hashWithSalt` 22

export
Hashable PrimType where
  hashWithSalt h = \case
    IntType     => h `hashWithSalt` 1
    Int8Type    => h `hashWithSalt` 2
    Int16Type   => h `hashWithSalt` 3
    Int32Type   => h `hashWithSalt` 4
    Int64Type   => h `hashWithSalt` 5
    IntegerType => h `hashWithSalt` 6
    Bits8Type   => h `hashWithSalt` 7
    Bits16Type  => h `hashWithSalt` 8
    Bits32Type  => h `hashWithSalt` 9
    Bits64Type  => h `hashWithSalt` 10
    StringType  => h `hashWithSalt` 11
    CharType    => h `hashWithSalt` 12
    DoubleType  => h `hashWithSalt` 13
    WorldType   => h `hashWithSalt` 14

export
Hashable Constant where
  hashWithSalt h = \case
    I i   => h `hashWithSalt` 0  `hashWithSalt` i
    I8 x  => h `hashWithSalt` 1  `hashWithSalt` x
    I16 x => h `hashWithSalt` 2  `hashWithSalt` x
    I32 x => h `hashWithSalt` 3  `hashWithSalt` x
    I64 x => h `hashWithSalt` 4  `hashWithSalt` x
    BI x  => h `hashWithSalt` 5  `hashWithSalt` x
    B8 x  => h `hashWithSalt` 6  `hashWithSalt` x
    B16 x => h `hashWithSalt` 7  `hashWithSalt` x
    B32 x => h `hashWithSalt` 8  `hashWithSalt` x
    B64 x => h `hashWithSalt` 9  `hashWithSalt` x
    Str x => h `hashWithSalt` 10 `hashWithSalt` x
    Ch x  => h `hashWithSalt` 11 `hashWithSalt` x
    Db x  => h `hashWithSalt` 12 `hashWithSalt` x
    PrT x => h `hashWithSalt` 13 `hashWithSalt` x

    WorldVal => h `hashWithSalt` 14

export
Hashable LazyReason where
  hashWithSalt h = \case
    LInf => h `hashWithSalt` 0
    LLazy => h `hashWithSalt` 1
    LUnknown => h `hashWithSalt` 2

export
Hashable (PrimFn arity) where
  hashWithSalt h = \case
    Add ty =>
      h `hashWithSalt` 0 `hashWithSalt` ty
    Sub ty =>
      h `hashWithSalt` 1 `hashWithSalt` ty
    Mul ty =>
      h `hashWithSalt` 2 `hashWithSalt` ty
    Div ty =>
      h `hashWithSalt` 3 `hashWithSalt` ty
    Mod ty =>
      h `hashWithSalt` 4 `hashWithSalt` ty
    Neg ty =>
      h `hashWithSalt` 5 `hashWithSalt` ty
    ShiftL ty =>
      h `hashWithSalt` 6 `hashWithSalt` ty
    ShiftR ty =>
      h `hashWithSalt` 7 `hashWithSalt` ty

    BAnd ty =>
      h `hashWithSalt` 8 `hashWithSalt` ty
    BOr ty =>
      h `hashWithSalt` 9 `hashWithSalt` ty
    BXOr ty =>
      h `hashWithSalt` 10 `hashWithSalt` ty

    LT ty =>
      h `hashWithSalt` 11 `hashWithSalt` ty
    LTE ty =>
      h `hashWithSalt` 12 `hashWithSalt` ty
    EQ ty =>
      h `hashWithSalt` 13 `hashWithSalt` ty
    GTE ty =>
      h `hashWithSalt` 14 `hashWithSalt` ty
    GT ty =>
      h `hashWithSalt` 15 `hashWithSalt` ty

    StrLength =>
      h `hashWithSalt` 16
    StrHead =>
      h `hashWithSalt` 17
    StrTail =>
      h `hashWithSalt` 18
    StrIndex =>
      h `hashWithSalt` 19
    StrCons =>
      h `hashWithSalt` 20
    StrAppend =>
      h `hashWithSalt` 21
    StrReverse =>
      h `hashWithSalt` 22
    StrSubstr =>
      h `hashWithSalt` 23

    DoubleExp =>
      h `hashWithSalt` 24
    DoubleLog =>
      h `hashWithSalt` 25
    DoubleSin =>
      h `hashWithSalt` 26
    DoubleCos =>
      h `hashWithSalt` 27
    DoubleTan =>
      h `hashWithSalt` 28
    DoubleASin =>
      h `hashWithSalt` 29
    DoubleACos =>
      h `hashWithSalt` 30
    DoubleATan =>
      h `hashWithSalt` 31
    DoubleSqrt =>
      h `hashWithSalt` 32
    DoubleFloor =>
      h `hashWithSalt` 33
    DoubleCeiling =>
      h `hashWithSalt` 34

    Cast f t =>
      h `hashWithSalt` 35 `hashWithSalt` f `hashWithSalt` t
    BelieveMe =>
      h `hashWithSalt` 36
    Crash =>
      h `hashWithSalt` 37

    DoublePow =>
      h `hashWithSalt` 38

export
Hashable ConInfo where
  hashWithSalt h = \case
    DATACON => h `hashWithSalt` 0
    TYCON => h `hashWithSalt` 1
    NIL => h `hashWithSalt` 2
    CONS => h `hashWithSalt` 3
    ENUM n => h `hashWithSalt` 4 `hashWithSalt` n
    NOTHING => h `hashWithSalt` 5
    JUST => h `hashWithSalt` 6
    RECORD => h `hashWithSalt` 7
    ZERO => h `hashWithSalt` 8
    SUCC => h `hashWithSalt` 9
    UNIT => h `hashWithSalt` 10

mutual
  export
  Hashable NamedCExp where
    hashWithSalt h = \case
      NmLocal fc n =>
        h `hashWithSalt` 0 `hashWithSalt` n
      NmRef fc n =>
        h `hashWithSalt` 1 `hashWithSalt` n
      NmLam fc x rhs =>
        h `hashWithSalt` 2 `hashWithSalt` x `hashWithSalt` rhs
      NmLet fc x val rhs =>
        h `hashWithSalt` 3 `hashWithSalt` x `hashWithSalt` val `hashWithSalt` rhs
      NmApp fc f xs =>
        h `hashWithSalt` 4 `hashWithSalt` f `hashWithSalt` xs
      NmCon fc cn ci t args =>
        h `hashWithSalt` 5 `hashWithSalt` cn `hashWithSalt` ci `hashWithSalt` t `hashWithSalt` args
      NmOp fc fn args =>
        h `hashWithSalt` 6 `hashWithSalt` fn `hashWithSalt` args
      NmExtPrim fc p args =>
        h `hashWithSalt` 7 `hashWithSalt` p `hashWithSalt` args
      NmForce fc r x =>
        h `hashWithSalt` 8 `hashWithSalt` r `hashWithSalt` x
      NmDelay fc r x =>
        h `hashWithSalt` 9 `hashWithSalt` r `hashWithSalt` x
      NmConCase fc sc alts df =>
        h `hashWithSalt` 10 `hashWithSalt` sc `hashWithSalt` alts `hashWithSalt` df
      NmConstCase fc sc alts df =>
        h `hashWithSalt` 11 `hashWithSalt` sc `hashWithSalt` alts `hashWithSalt` df
      NmPrimVal fc c =>
        h `hashWithSalt` 12 `hashWithSalt` c
      NmErased fc =>
        h `hashWithSalt` 13
      NmCrash fc msg =>
        h `hashWithSalt` 14 `hashWithSalt` msg

  export
  Hashable NamedConAlt where
    hashWithSalt h (MkNConAlt n ci tag args rhs) =
      h `hashWithSalt` n `hashWithSalt` ci `hashWithSalt` tag `hashWithSalt` args `hashWithSalt` rhs

  export
  Hashable NamedConstAlt where
    hashWithSalt h (MkNConstAlt c rhs) =
      h `hashWithSalt` c `hashWithSalt` rhs

export
Hashable NamedDef where
  hashWithSalt h = \case
    MkNmFun args ce =>
      h `hashWithSalt` 0 `hashWithSalt` args `hashWithSalt` ce
    MkNmCon tag arity nt =>
      h `hashWithSalt` 1 `hashWithSalt` tag `hashWithSalt` arity `hashWithSalt` nt
    MkNmForeign ccs fargs cft =>
      h `hashWithSalt` 2 `hashWithSalt` ccs `hashWithSalt` fargs `hashWithSalt` cft
    MkNmError e =>
      h `hashWithSalt` 3 `hashWithSalt` e
