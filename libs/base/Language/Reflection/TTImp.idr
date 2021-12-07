module Language.Reflection.TTImp

import public Language.Reflection.TT

%default total

-- Unchecked terms and declarations in the intermediate language
mutual
  public export
  data BindMode = PI Count | PATTERN | COVERAGE | NONE

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
                 | UnderAppliedCon

  public export
  data TTImp : Type where
       IVar : FC -> Name -> TTImp
       IPi : FC -> Count -> PiInfo TTImp -> Maybe Name ->
             (argTy : TTImp) -> (retTy : TTImp) -> TTImp
       ILam : FC -> Count -> PiInfo TTImp -> Maybe Name ->
              (argTy : TTImp) -> (lamTy : TTImp) -> TTImp
       ILet : FC -> (lhsFC : FC) -> Count -> Name ->
              (nTy : TTImp) -> (nVal : TTImp) ->
              (scope : TTImp) -> TTImp
       ICase : FC -> TTImp -> (ty : TTImp) ->
               List Clause -> TTImp
       ILocal : FC -> List Decl -> TTImp -> TTImp
       IUpdate : FC -> List IFieldUpdate -> TTImp -> TTImp

       IApp : FC -> TTImp -> TTImp -> TTImp
       INamedApp : FC -> TTImp -> Name -> TTImp -> TTImp
       IAutoApp : FC -> TTImp -> TTImp -> TTImp
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
       IAs : FC -> (nameFC : FC) -> UseSide -> Name -> TTImp -> TTImp
       -- A 'dot' pattern, i.e. one which must also have the given value
       -- by unification
       IMustUnify : FC -> DotReason -> TTImp -> TTImp

       -- Laziness annotations
       IDelayed : FC -> LazyReason -> TTImp -> TTImp -- the type
       IDelay : FC -> TTImp -> TTImp -- delay constructor
       IForce : FC -> TTImp -> TTImp

       -- Quasiquotation
       IQuote : FC -> TTImp -> TTImp
       IQuoteName : FC -> Name -> TTImp
       IQuoteDecl : FC -> List Decl -> TTImp
       IUnquote : FC -> TTImp -> TTImp

       IPrimVal : FC -> (c : Constant) -> TTImp
       IType : FC -> TTImp
       IHole : FC -> String -> TTImp

       -- An implicit value, solved by unification, but which will also be
       -- bound (either as a pattern variable or a type variable) if unsolved
       -- at the end of elaborator
       Implicit : FC -> (bindIfUnsolved : Bool) -> TTImp
       IWithUnambigNames : FC -> List Name -> TTImp -> TTImp

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
  data NoMangleDirective : Type where
     CommonName : String -> NoMangleDirective
     BackendNames : List (String, String) -> NoMangleDirective

  public export
  data FnOpt : Type where
       Inline : FnOpt
       NoInline : FnOpt
       Deprecate : FnOpt
       TCInline : FnOpt
       -- Flag means the hint is a direct hint, not a function which might
       -- find the result (e.g. chasing parent interface dictionaries)
       Hint : Bool -> FnOpt
       -- Flag means to use as a default if all else fails
       GlobalHint : Bool -> FnOpt
       ExternFn : FnOpt
       -- Defined externally, list calling conventions
       ForeignFn : List TTImp -> FnOpt
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt
       Totality : TotalReq -> FnOpt
       Macro : FnOpt
       SpecArgs : List Name -> FnOpt
       ||| Keep the user provided name during codegen
       NoMangle : NoMangleDirective -> FnOpt

  public export
  data ITy : Type where
       MkTy : FC -> (nameFC : FC) -> (n : Name) -> (ty : TTImp) -> ITy

  public export
  data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors
       UniqueSearch : DataOpt -- auto implicit search must check result is unique
       External : DataOpt -- implemented externally
       NoNewtype : DataOpt -- don't apply newtype optimisation

  public export
  data Data : Type where
       MkData : FC -> (n : Name) -> (tycon : TTImp) ->
                (opts : List DataOpt) ->
                (datacons : List ITy) -> Data
       MkLater : FC -> (n : Name) -> (tycon : TTImp) -> Data

  public export
  data IField : Type where
       MkIField : FC -> Count -> PiInfo TTImp -> Name -> TTImp ->
                  IField

  public export
  data Record : Type where
       MkRecord : FC -> (n : Name) ->
                  (params : List (Name, Count, PiInfo TTImp, TTImp)) ->
                  (conName : Name) ->
                  (fields : List IField) ->
                  Record

  public export
  data WithFlag = Syntactic

  public export
  data Clause : Type where
       PatClause : FC -> (lhs : TTImp) -> (rhs : TTImp) -> Clause
       WithClause : FC -> (lhs : TTImp) -> (wval : TTImp) ->
                    (prf : Maybe Name) -> (flags : List WithFlag) ->
                    List Clause -> Clause
       ImpossibleClause : FC -> (lhs : TTImp) -> Clause

  public export
  data Decl : Type where
       IClaim : FC -> Count -> Visibility -> List FnOpt ->
                ITy -> Decl
       IData : FC -> Visibility -> Data -> Maybe TotalReq -> Decl
       IDef : FC -> Name -> List Clause -> Decl
       IParameters : FC -> List (Name, Count, PiInfo TTImp, TTImp) ->
                     List Decl -> Decl
       IRecord : FC ->
                 Maybe String -> -- nested namespace
                 Visibility -> Maybe TotalReq -> Record -> Decl
       INamespace : FC -> Namespace -> List Decl -> Decl
       ITransform : FC -> Name -> TTImp -> TTImp -> Decl
       IRunElabDecl : FC -> TTImp -> Decl
       ILog : Maybe (List String, Nat) -> Decl
       IBuiltin : FC -> BuiltinType -> Name -> Decl

public export
getFC : TTImp -> FC
getFC (IVar fc y)                = fc
getFC (IPi fc _ _ _ _ _)         = fc
getFC (ILam fc _ _ _ _ _)        = fc
getFC (ILet fc _ _ _ _ _ _)      = fc
getFC (ICase fc _ _ _)           = fc
getFC (ILocal fc _ _)            = fc
getFC (IUpdate fc _ _)           = fc
getFC (IApp fc _ _)              = fc
getFC (INamedApp fc _ _ _)       = fc
getFC (IAutoApp fc _ _)          = fc
getFC (IWithApp fc _ _)          = fc
getFC (ISearch fc _)             = fc
getFC (IAlternative fc _ _)      = fc
getFC (IRewrite fc _ _)          = fc
getFC (IBindHere fc _ _)         = fc
getFC (IBindVar fc _)            = fc
getFC (IAs fc _ _ _ _)           = fc
getFC (IMustUnify fc _ _)        = fc
getFC (IDelayed fc _ _)          = fc
getFC (IDelay fc _)              = fc
getFC (IForce fc _)              = fc
getFC (IQuote fc _)              = fc
getFC (IQuoteName fc _)          = fc
getFC (IQuoteDecl fc _)          = fc
getFC (IUnquote fc _)            = fc
getFC (IPrimVal fc _)            = fc
getFC (IType fc)                 = fc
getFC (IHole fc _)               = fc
getFC (Implicit fc _)            = fc
getFC (IWithUnambigNames fc _ _) = fc
