module Language.Reflection.TT

public export
FilePos : Type
FilePos = (Int, Int)

public export
data FC : Type where
     MkFC : String -> FilePos -> FilePos -> FC
     EmptyFC : FC

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
    | Str String
    | Ch Char
    | Db Double
    | WorldVal

    | IntType
    | IntegerType
    | StringType
    | CharType
    | DoubleType
    | WorldType

public export
data Name = UN String
          | MN String Int
          | NS (List String) Name

public export
data Count = M0 | M1 | MW

public export
data PiInfo = ImplicitArg | ExplicitArg | AutoImplicit

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
data LazyReason = LInf | LLazy | LUnknown

-- Type checked terms in the core TT
public export
data TT : List Name -> Type where
     Local : FC -> (idx : Nat) -> (n : Name) ->
             (0 prf : IsVar name idx vars) -> TT vars
     Ref : FC -> NameType -> Name -> TT vars
     Pi : FC -> Count -> PiInfo ->
          (x : Name) -> (argTy : TT vars) -> (retTy : TT (x :: vars)) ->
          TT vars
     Lam : FC -> Count -> PiInfo ->
           (x : Name) -> (argTy : TT vars) -> (scope : TT (x :: vars)) ->
           TT vars
     App : FC -> TT vars -> TT vars -> TT vars
     TDelayed : FC -> LazyReason -> TT vars -> TT vars
     TDelay : FC -> LazyReason -> (ty : TT vars) -> (arg : TT vars) -> TT vars
     TForce : FC -> TT vars -> TT vars
     PrimVal : FC -> Constant -> TT vars
     Erased : FC -> TT vars
     TType : FC -> TT vars

public export
data Visibility = Private | Export | Public

