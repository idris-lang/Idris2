module Language.Reflection.TT

import public Data.List
import public Data.String

import Decidable.Equality

%default total

public export
data Namespace = MkNS (List String) -- namespace, stored in reverse order

%name Namespace ns

public export
data ModuleIdent = MkMI (List String) -- module identifier, stored in reverse order

%name ModuleIdent mi

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Namespace where
  show (MkNS ns) = showSep "." (reverse ns)

-- 'FilePos' represents the position of
-- the source information in the file (or REPL).
-- in the form of '(line-no, column-no)'.
public export
FilePos : Type
FilePos = (Int, Int)

public export
data VirtualIdent : Type where
  Interactive : VirtualIdent

public export
data OriginDesc : Type where
  ||| Anything that originates in physical Idris source files is assigned a
  ||| `PhysicalIdrSrc modIdent`,
  |||   where `modIdent` is the top-level module identifier of that file.
  PhysicalIdrSrc : (ident : ModuleIdent) -> OriginDesc
  ||| Anything parsed from a package file is decorated with `PhysicalPkgSrc fname`,
  |||   where `fname` is path to the package file.
  PhysicalPkgSrc : (fname : String) -> OriginDesc
  Virtual : (ident : VirtualIdent) -> OriginDesc

%name OriginDesc origin

||| A file context is a filename together with starting and ending positions.
||| It's often carried by AST nodes that might have been created from a source
||| file or by the compiler. That makes it useful to have the notion of
||| `EmptyFC` as part of the type.
public export
data FC = MkFC        OriginDesc FilePos FilePos
        | ||| Virtual FCs are FC attached to desugared/generated code. They can help with marking
          ||| errors, but we shouldn't attach semantic highlighting metadata to them.
          MkVirtualFC OriginDesc FilePos FilePos
        | EmptyFC

%name FC fc

public export
emptyFC : FC
emptyFC = EmptyFC

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon   : (tag : Int) -> (arity : Nat) -> NameType

%name NameType nty

public export
data PrimType
    = IntType
    | IntegerType
    | Int8Type
    | Int16Type
    | Int32Type
    | Int64Type
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
    = I Int
    | BI Integer
    | I8 Int8
    | I16 Int16
    | I32 Int32
    | I64 Int64
    | B8 Bits8
    | B16 Bits16
    | B32 Bits32
    | B64 Bits64
    | Str String
    | Ch Char
    | Db Double
    | PrT PrimType
    | WorldVal

%name Constant c

export
Show PrimType where
  show IntType = "Int"
  show IntegerType = "Integer"
  show Int8Type = "Int8"
  show Int16Type = "Int16"
  show Int32Type = "Int32"
  show Int64Type = "Int64"
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
  show (BI x) = show x
  show (I8 x) = show x
  show (I16 x) = show x
  show (I32 x) = show x
  show (I64 x) = show x
  show (B8 x) = show x
  show (B16 x) = show x
  show (B32 x) = show x
  show (B64 x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show (PrT x) = show x
  show WorldVal = "%World"

public export
data UserName
  = Basic String -- default name constructor       e.g. map
  | Field String -- field accessor                 e.g. .fst
  | Underscore   -- no name                        e.g. _

%name UserName un

public export
data Name = NS Namespace Name -- name in a namespace
          | UN UserName -- user defined name
          | MN String Int -- machine generated name
          | DN String Name -- a name and how to display it
          | Nested (Int, Int) Name -- nested function name
          | CaseBlock String Int -- case block nested in (resolved) name
          | WithBlock String Int -- with block nested in (resolved) name

%name Name nm

export
dropNS : Name -> Name
dropNS (NS _ n) = dropNS n
dropNS n = n

export
isOp : Name -> Bool
isOp nm = case dropNS nm of
  UN (Basic n) => case strM n of
    StrCons c _ => not (isAlpha c)
    _ => False
  _ => False

export
Show UserName where
  show (Basic n) = n
  show (Field n) = "." ++ n
  show Underscore = "_"

export
showPrefix : Bool -> Name -> String
showPrefix b nm@(UN un) = showParens (b && isOp nm) (show un)
showPrefix b (NS ns n) = show ns ++ "." ++ showPrefix True n
showPrefix b (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
showPrefix b (DN str y) = str
showPrefix b (Nested (outer, idx) inner)
      = show outer ++ ":" ++ show idx ++ ":" ++ showPrefix False inner
showPrefix b (CaseBlock outer i) = "case block in " ++ show outer
showPrefix b (WithBlock outer i) = "with block in " ++ show outer

export
Show Name where
  show = showPrefix False

public export
record NameInfo where
  constructor MkNameInfo
  nametype : NameType

public export
data Count = M0 | M1 | MW
%name Count rig

export
enunciate : Count -> String
enunciate M0 = "runtime irrelevant"
enunciate M1 = "linear"
enunciate MW = "unconstrained"

export
showCount : Count -> String -> String
showCount M0 s = "0 \{s}"
showCount M1 s = "1 \{s}"
showCount MW s = s

public export
data PiInfo t = ImplicitArg | ExplicitArg | AutoImplicit | DefImplicit t
%name PiInfo pinfo

export
showPiInfo : Show a => {default True wrapExplicit : Bool} -> PiInfo a -> String -> String
showPiInfo ImplicitArg s = "{\{s}}"
showPiInfo ExplicitArg s = if wrapExplicit then "(\{s})" else s
showPiInfo AutoImplicit s = "{auto \{s}}"
showPiInfo (DefImplicit t) s = "{default \{assert_total $ showPrec App t} \{s}}"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)
%name IsVar idx

public export
data LazyReason = LInf | LLazy | LUnknown
%name LazyReason lr

export
Show LazyReason where
  show LInf = "Inf"
  show LLazy = "Lazy"
  show LUnknown = "Unknown"

public export
data TotalReq = Total | CoveringOnly | PartialOK
%name TotalReq treq

export
Show TotalReq where
  show Total = "total"
  show CoveringOnly = "covering"
  show PartialOK = "partial"

export
showTotalReq : Maybe TotalReq -> String -> String
showTotalReq Nothing s = s
showTotalReq (Just treq) s = unwords [show treq, s]

public export
data Visibility = Private | Export | Public
%name Visibility vis

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

public export
data BuiltinType = BuiltinNatural | NaturalToInteger | IntegerToNatural
%name BuiltinType bty

export
Show BuiltinType where
  show BuiltinNatural = "Natural"
  show NaturalToInteger = "NaturalToInteger"
  show IntegerToNatural = "IntegerToNatural"

public export
Eq TotalReq where
  Total        == Total        = True
  CoveringOnly == CoveringOnly = True
  PartialOK    == PartialOK    = True
  _ == _ = False

public export
Eq Visibility where
  Private == Private = True
  Export  == Export  = True
  Public  == Public  = True
  _ == _ = False

public export
Eq BuiltinType where
  BuiltinNatural   == BuiltinNatural = True
  NaturalToInteger == NaturalToInteger = True
  IntegerToNatural == IntegerToNatural = True
  _ == _ = False


public export
Eq LazyReason where
  LInf     == LInf     = True
  LLazy    == LLazy    = True
  LUnknown == LUnknown = True
  _ == _ = False

public export
Eq Namespace where
  MkNS ns == MkNS ns' = ns == ns'

public export
Eq Count where
  M0 == M0 = True
  M1 == M1 = True
  MW == MW = True
  _  == _  = False

public export
Eq UserName where
  Basic n    == Basic n'   = n == n'
  Field n    == Field n'   = n == n'
  Underscore == Underscore = True
  _ == _ = False

public export
Eq Name where
  NS ns n        == NS ns' n'       = ns == ns' && n == n'
  UN n           == UN n'           = n == n'
  MN n i         == MN n' i'        = n == n' && i == i'
  DN _ n         == DN _ n'         = n == n'
  Nested i n     == Nested i' n'    = i == i' && n == n'
  CaseBlock n i  == CaseBlock n' i' = n == n' && i == i'
  WithBlock n i  == WithBlock n' i' = n == n' && i == i'
  _ == _ = False

public export
Eq PrimType where
  IntType     == IntType     = True
  IntegerType == IntegerType = True
  Int8Type    == Int8Type    = True
  Int16Type   == Int16Type   = True
  Int32Type   == Int32Type   = True
  Int64Type   == Int64Type   = True
  Bits8Type   == Bits8Type   = True
  Bits16Type  == Bits16Type  = True
  Bits32Type  == Bits32Type  = True
  Bits64Type  == Bits64Type  = True
  StringType  == StringType  = True
  CharType    == CharType    = True
  DoubleType  == DoubleType  = True
  WorldType   == WorldType   = True
  _ == _ = False

public export
Eq Constant where
  I c         == I c'        = c == c'
  BI c        == BI c'       = c == c'
  I8 c        == I8 c'       = c == c'
  I16 c       == I16 c'      = c == c'
  I32 c       == I32 c'      = c == c'
  I64 c       == I64 c'      = c == c'
  B8 c        == B8 c'       = c == c'
  B16 c       == B16 c'      = c == c'
  B32 c       == B32 c'      = c == c'
  B64 c       == B64 c'      = c == c'
  Str c       == Str c'      = c == c'
  Ch c        == Ch c'       = c == c'
  Db c        == Db c'       = c == c'
  PrT t       == PrT t'      = t == t'
  WorldVal    == WorldVal    = True
  _ == _ = False

export Injective MkNS where injective Refl = Refl

public export
DecEq Namespace where
  decEq (MkNS ns) (MkNS ns') = decEqCong (decEq ns ns')

export Injective Basic where injective Refl = Refl
export Injective Field where injective Refl = Refl

public export
DecEq UserName where
  decEq (Basic str) (Basic str1) = decEqCong (decEq str str1)
  decEq (Basic str) (Field str1) = No (\case Refl impossible)
  decEq (Basic str) Underscore = No (\case Refl impossible)
  decEq (Field str) (Basic str1) = No (\case Refl impossible)
  decEq (Field str) (Field str1) = decEqCong (decEq str str1)
  decEq (Field str) Underscore = No (\case Refl impossible)
  decEq Underscore (Basic str) = No (\case Refl impossible)
  decEq Underscore (Field str) = No (\case Refl impossible)
  decEq Underscore Underscore = Yes Refl

export Biinjective NS where biinjective Refl = (Refl, Refl)
export Injective UN where injective Refl = Refl
export Biinjective MN where biinjective Refl = (Refl, Refl)
export Biinjective DN where biinjective Refl = (Refl, Refl)
export Biinjective Nested where biinjective Refl = (Refl, Refl)
export Biinjective CaseBlock where biinjective Refl = (Refl, Refl)
export Biinjective WithBlock where biinjective Refl = (Refl, Refl)

public export
DecEq Name where
  decEq (NS ns nm) (NS ns1 nm1) = decEqCong2 (decEq ns ns1) (decEq nm nm1)
  decEq (NS ns nm) (UN un) =  No (\case Refl impossible)
  decEq (NS ns nm) (MN str i) = No (\case Refl impossible)
  decEq (NS ns nm) (DN str nm1) = No (\case Refl impossible)
  decEq (NS ns nm) (Nested x nm1) = No (\case Refl impossible)
  decEq (NS ns nm) (CaseBlock str i) = No (\case Refl impossible)
  decEq (NS ns nm) (WithBlock str i) = No (\case Refl impossible)
  decEq (UN un) (NS ns nm) = No (\case Refl impossible)
  decEq (UN un) (UN un1) = decEqCong (decEq un un1)
  decEq (UN un) (MN str i) = No (\case Refl impossible)
  decEq (UN un) (DN str nm) = No (\case Refl impossible)
  decEq (UN un) (Nested x nm) = No (\case Refl impossible)
  decEq (UN un) (CaseBlock str i) = No (\case Refl impossible)
  decEq (UN un) (WithBlock str i) = No (\case Refl impossible)
  decEq (MN str i) (NS ns nm) = No (\case Refl impossible)
  decEq (MN str i) (UN un) = No (\case Refl impossible)
  decEq (MN str i) (MN str1 j) = decEqCong2 (decEq str str1) (decEq i j)
  decEq (MN str i) (DN str1 nm) = No (\case Refl impossible)
  decEq (MN str i) (Nested x nm) = No (\case Refl impossible)
  decEq (MN str i) (CaseBlock str1 j) = No (\case Refl impossible)
  decEq (MN str i) (WithBlock str1 j) = No (\case Refl impossible)
  decEq (DN str nm) (NS ns nm1) = No (\case Refl impossible)
  decEq (DN str nm) (UN un) = No (\case Refl impossible)
  decEq (DN str nm) (MN str1 i) = No (\case Refl impossible)
  decEq (DN str nm) (DN str1 nm1) = decEqCong2 (decEq str str1) (decEq nm nm1)
  decEq (DN str nm) (Nested x nm1) = No (\case Refl impossible)
  decEq (DN str nm) (CaseBlock str1 i) = No (\case Refl impossible)
  decEq (DN str nm) (WithBlock str1 i) = No (\case Refl impossible)
  decEq (Nested x nm) (NS ns nm1) = No (\case Refl impossible)
  decEq (Nested x nm) (UN un) = No (\case Refl impossible)
  decEq (Nested x nm) (MN str i) = No (\case Refl impossible)
  decEq (Nested x nm) (DN str nm1) = No (\case Refl impossible)
  decEq (Nested x nm) (Nested y nm1) = decEqCong2 (decEq x y) (decEq nm nm1)
  decEq (Nested x nm) (CaseBlock str i) = No (\case Refl impossible)
  decEq (Nested x nm) (WithBlock str i) = No (\case Refl impossible)
  decEq (CaseBlock str i) (NS ns nm) = No (\case Refl impossible)
  decEq (CaseBlock str i) (UN un) = No (\case Refl impossible)
  decEq (CaseBlock str i) (MN str1 j) = No (\case Refl impossible)
  decEq (CaseBlock str i) (DN str1 nm) = No (\case Refl impossible)
  decEq (CaseBlock str i) (Nested x nm) = No (\case Refl impossible)
  decEq (CaseBlock str i) (CaseBlock str1 j) = decEqCong2 (decEq str str1) (decEq i j)
  decEq (CaseBlock str i) (WithBlock str1 j) = No (\case Refl impossible)
  decEq (WithBlock str i) (NS ns nm) = No (\case Refl impossible)
  decEq (WithBlock str i) (UN un) = No (\case Refl impossible)
  decEq (WithBlock str i) (MN str1 j) = No (\case Refl impossible)
  decEq (WithBlock str i) (DN str1 nm) = No (\case Refl impossible)
  decEq (WithBlock str i) (Nested x nm) = No (\case Refl impossible)
  decEq (WithBlock str i) (CaseBlock str1 j) = No (\case Refl impossible)
  decEq (WithBlock str i) (WithBlock str1 j) = decEqCong2 (decEq str str1) (decEq i j)
