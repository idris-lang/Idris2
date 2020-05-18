module Language.Reflection.TTImp

import Language.Reflection.TT

-- Unchecked terms and declarations in the intermediate language
mutual
  public export
  data BindMode = PI Count | PATTERN | NONE

  -- For as patterns matching linear arguments, select which side is
  -- consumed
  public export
  data UseSide = UseLeft | UseRight

  public export
  data DotReason = NonLinearVar
                 | VarApplied
                 | NotConstructor
                 | ErasedArg
                 | UserDotted
                 | UnknownDot

  public export
  data TTImp : Type where
       IVar : FC -> Name -> TTImp
       IPi : FC -> Count -> PiInfo -> Maybe Name ->
             (argTy : TTImp) -> (retTy : TTImp) -> TTImp
       ILam : FC -> Count -> PiInfo -> Maybe Name ->
              (argTy : TTImp) -> (lamTy : TTImp) -> TTImp
       ILet : FC -> Count -> Name ->
              (nTy : TTImp) -> (nVal : TTImp) ->
              (scope : TTImp) -> TTImp
       ICase : FC -> TTImp -> (ty : TTImp) ->
               List Clause -> TTImp
       ILocal : FC -> List Decl -> TTImp -> TTImp
       IUpdate : FC -> List IFieldUpdate -> TTImp -> TTImp

       IApp : FC -> TTImp -> TTImp -> TTImp
       IImplicitApp : FC -> TTImp -> Maybe Name -> TTImp -> TTImp
       IWithApp : FC -> TTImp -> TTImp -> TTImp

       ISearch : FC -> (depth : Nat) -> TTImp
       IAlternative : FC -> AltType -> List TTImp -> TTImp
       IRewrite : FC -> TTImp -> TTImp -> TTImp

       -- Any implicit bindings in the scope should be bound here, using
       -- the given binder
       IBindHere : FC -> BindMode -> TTImp -> TTImp
       -- A name which should be implicitly bound
       IBindVar : FC -> String -> TTImp
       -- An 'as' pattern, valid on the LHS of a clause only
       IAs : FC -> UseSide -> Name -> TTImp -> TTImp
       -- A 'dot' pattern, i.e. one which must also have the given value
       -- by unification
       IMustUnify : FC -> DotReason -> TTImp -> TTImp

       -- Laziness annotations
       IDelayed : FC -> LazyReason -> TTImp -> TTImp -- the type
       IDelay : FC -> TTImp -> TTImp -- delay constructor
       IForce : FC -> TTImp -> TTImp

       -- Quasiquotation
       IQuote : FC -> TTImp -> TTImp
       IQuoteDecl : FC -> TTImp -> TTImp
       IUnquote : FC -> TTImp -> TTImp

       IPrimVal : FC -> (c : Constant) -> TTImp
       IType : FC -> TTImp
       IHole : FC -> String -> TTImp

       -- An implicit value, solved by unification, but which will also be
       -- bound (either as a pattern variable or a type variable) if unsolved
       -- at the end of elaborator
       Implicit : FC -> (bindIfUnsolved : Bool) -> TTImp

  public export
  data IFieldUpdate : Type where
       ISetField : (path : List String) -> TTImp -> IFieldUpdate
       ISetFieldApp : (path : List String) -> TTImp -> IFieldUpdate

  public export
  data AltType : Type where
       FirstSuccess : AltType
       Unique : AltType
       UniqueDefault : TTImp -> AltType

  public export
  data FnOpt : Type where
       Inline : FnOpt
       -- Flag means the hint is a direct hint, not a function which might
       -- find the result (e.g. chasing parent interface dictionaries)
       Hint : Bool -> FnOpt
       -- Flag means to use as a default if all else fails
       GlobalHint : Bool -> FnOpt
       ExternFn : FnOpt
       -- Defined externally, list calling conventions
       ForeignFn : List String -> FnOpt
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt
       Total : FnOpt
       Covering : FnOpt
       PartialOK : FnOpt
       Macro : FnOpt

  public export
  data ITy : Type where
       MkTy : FC -> (n : Name) -> (ty : TTImp) -> ITy

  public export
  data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors
       UniqueSearch : DataOpt

  public export
  data Data : Type where
       MkData : FC -> (n : Name) -> (tycon : TTImp) ->
                (opts : List DataOpt) ->
                (datacons : List ITy) -> Data
       MkLater : FC -> (n : Name) -> (tycon : TTImp) -> Data

  public export
  data IField : Type where
       MkIField : FC -> Count -> PiInfo -> Name -> TTImp ->
                  IField

  public export
  data Record : Type where
       MkRecord : FC -> (n : Name) ->
                  (params : List (Name, TTImp)) ->
                  (conName : Maybe Name) ->
                  (fields : List IField) ->
                  Record

  public export
  data Clause : Type where
       PatClause : FC -> (lhs : TTImp) -> (rhs : TTImp) -> Clause
       WithClause : FC -> (lhs : TTImp) -> (wval : TTImp) ->
                    List Clause -> Clause
       ImpossibleClause : FC -> (lhs : TTImp) -> Clause

  public export
  data Decl : Type where
       IClaim : FC -> Count -> Visibility -> List FnOpt ->
                ITy -> Decl
       IData : FC -> Visibility -> Data -> Decl
       IDef : FC -> Name -> List Clause -> Decl
       IParameters : FC -> List (Name, TTImp) ->
                     List Decl -> Decl
       IRecord : FC -> Visibility -> Record -> Decl
       INamespace : FC ->
                    (nested : Bool) ->
                      -- ^ if True, parent namespaces in the same file can also
                      -- look inside and see private/export names in full
                    List String -> List Decl -> Decl
       ITransform : FC -> TTImp -> TTImp -> Decl
       ILog : Nat -> Decl
