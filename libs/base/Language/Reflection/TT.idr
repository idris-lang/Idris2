module Language.Reflection.TT

import public Data.List
import Data.String

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
Show Name where
  show (NS ns n) = show ns ++ "." ++ show n
  show (UN x) = show x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (DN str y) = str
  show (Nested (outer, idx) inner)
      = show outer ++ ":" ++ show idx ++ ":" ++ show inner
  show (CaseBlock outer i) = "case block in " ++ show outer
  show (WithBlock outer i) = "with block in " ++ show outer

public export
record NameInfo where
  constructor MkNameInfo
  nametype : NameType

public export
data Count = M0 | M1 | MW
%name Count rig

export
showCount : Count -> String -> String
showCount M0 s = "0 \{s}"
showCount M1 s = "1 \{s}"
showCount MW s = s

public export
data PiInfo t = ImplicitArg | ExplicitArg | AutoImplicit | DefImplicit t
%name PiInfo pinfo

export
showPiInfo : Show a => PiInfo a -> String -> String
showPiInfo ImplicitArg s = "{\{s}}"
showPiInfo ExplicitArg s = "(\{s})"
showPiInfo AutoImplicit s = "{auto \{s}}"
showPiInfo (DefImplicit t) s = "{default \{assert_total (show t)} \{s}}"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)
%name IsVar idx

public export
data LazyReason = LInf | LLazy | LUnknown
%name LazyReason lr

export
data TT : Type where [external]
%name TT s, t, u

{-
-- Type checked terms in the core TT
public export
data TT : List Name -> Type where
     Local : FC -> (idx : Nat) -> (0 prf : IsVar name idx vars) -> TT vars
     Ref : FC -> NameType -> Name -> TT vars
     Pi : FC -> Count -> PiInfo (TT vars) ->
          (x : Name) -> (argTy : TT vars) -> (retTy : TT (x :: vars)) ->
          TT vars
     Lam : FC -> Count -> PiInfo (TT vars) ->
           (x : Name) -> (argTy : TT vars) -> (scope : TT (x :: vars)) ->
           TT vars
     App : FC -> TT vars -> TT vars -> TT vars
     TDelayed : FC -> LazyReason -> TT vars -> TT vars
     TDelay : FC -> LazyReason -> (ty : TT vars) -> (arg : TT vars) -> TT vars
     TForce : FC -> LazyReason -> TT vars -> TT vars
     PrimVal : FC -> Constant -> TT vars
     Erased : FC -> TT vars
     TType : FC -> TT vars
     -}

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
