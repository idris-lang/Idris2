module Language.Reflection.TT

import public Data.List

%default total

public export
data Namespace = MkNS (List String) -- namespace, stored in reverse order

public export
data ModuleIdent = MkMI (List String) -- module identifier, stored in reverse order

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

public export
emptyFC : FC
emptyFC = EmptyFC

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon   : (tag : Int) -> (arity : Nat) -> NameType

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
    | WorldVal

    | IntType
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

public export
data UserName
  = Basic String -- default name constructor       e.g. map
  | Field String -- field accessor                 e.g. .fst
  | Underscore   -- no name                        e.g. _

public export
data Name = NS Namespace Name -- name in a namespace
          | UN UserName -- user defined name
          | MN String Int -- machine generated name
          | DN String Name -- a name and how to display it
          | Nested (Int, Int) Name -- nested function name
          | CaseBlock String Int -- case block nested in (resolved) name
          | WithBlock String Int -- with block nested in (resolved) name

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
data Count = M0 | M1 | MW

public export
data PiInfo t = ImplicitArg | ExplicitArg | AutoImplicit | DefImplicit t

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
data LazyReason = LInf | LLazy | LUnknown

export
data TT : Type where [external]

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

public export
data Visibility = Private | Export | Public

public export
data BuiltinType = BuiltinNatural | NaturalToInteger | IntegerToNatural
