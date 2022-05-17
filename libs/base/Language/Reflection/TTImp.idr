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
       IWithUnambigNames : FC -> List (FC, Name) -> TTImp -> TTImp

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
       -- Mark for export to a foreign language, list calling conventions
       ForeignExport : List TTImp -> FnOpt
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt
       Totality : TotalReq -> FnOpt
       Macro : FnOpt
       SpecArgs : List Name -> FnOpt
       ||| Keep the user provided name during codegen
       NoMangle : Maybe NoMangleDirective -> FnOpt

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
       WithClause : FC -> (lhs : TTImp) ->
                    (rig : Count) -> (wval : TTImp) -> -- with'd expression (& quantity)
                    (prf : Maybe Name) -> -- optional name for the proof
                    (flags : List WithFlag) ->
                    List Clause -> Clause
       ImpossibleClause : FC -> (lhs : TTImp) -> Clause

  public export
  data Decl : Type where
       IClaim : FC -> Count -> Visibility -> List FnOpt ->
                ITy -> Decl
       IData : FC -> Visibility -> Maybe TotalReq -> Data -> Decl
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
Eq BindMode where
  PI c    == PI c'   = c == c'
  PATTERN == PATTERN = True
  NONE    == NONE    = True
  _ == _ = False

public export
Eq UseSide where
  UseLeft  == UseLeft  = True
  UseRight == UseRight = True
  _ == _ = False

public export
Eq DotReason where
  NonLinearVar    == NonLinearVar    = True
  VarApplied      == VarApplied      = True
  NotConstructor  == NotConstructor  = True
  ErasedArg       == ErasedArg       = True
  UserDotted      == UserDotted      = True
  UnknownDot      == UnknownDot      = True
  UnderAppliedCon == UnderAppliedCon = True
  _ == _ = False

public export
Eq WithFlag where
  Syntactic == Syntactic = True

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

public export
Eq DataOpt where
  SearchBy ns == SearchBy ns' = ns == ns'
  NoHints == NoHints = True
  UniqueSearch == UniqueSearch = True
  External == External = True
  NoNewtype == NoNewtype = True
  _ == _ = False

public export
Eq NoMangleDirective where
  CommonName s == CommonName s' = s == s'
  BackendNames ns == BackendNames ns' = ns == ns'
  _ == _ = False

public export
Eq a => Eq (PiInfo a) where
  ImplicitArg   == ImplicitArg = True
  ExplicitArg   == ExplicitArg = True
  AutoImplicit  == AutoImplicit = True
  DefImplicit t == DefImplicit t' = t == t'
  _ == _ = False

parameters {auto eqTTImp : Eq TTImp}
  public export
  Eq Clause where
    PatClause _ lhs rhs == PatClause _ lhs' rhs' =
      lhs == lhs' && rhs == rhs'
    WithClause _ l r w p f cs == WithClause _ l' r' w' p' f' cs' =
      l == l' && r == r' && w == w' && p == p' && f == f' && (assert_total $ cs == cs')
    ImpossibleClause _ l == ImpossibleClause _ l' = l == l'
    _ == _ = False

  public export
  Eq IFieldUpdate where
    ISetField p t == ISetField p' t' =
      p == p' && t == t'
    ISetFieldApp p t == ISetFieldApp p' t' =
      p == p' && t == t'
    _ == _ = False

  public export
  Eq AltType where
    FirstSuccess    == FirstSuccess     = True
    Unique          == Unique           = True
    UniqueDefault t == UniqueDefault t' = t == t'
    _ == _ = False

  public export
  Eq FnOpt where
    Inline == Inline = True
    NoInline == NoInline = True
    Deprecate == Deprecate = True
    TCInline == TCInline = True
    Hint b == Hint b' = b == b'
    GlobalHint b == GlobalHint b' = b == b'
    ExternFn == ExternFn = True
    ForeignFn es == ForeignFn es' = es == es'
    ForeignExport es == ForeignExport es' = es == es'
    Invertible == Invertible = True
    Totality tr == Totality tr' = tr == tr'
    Macro == Macro = True
    SpecArgs ns == SpecArgs ns' = ns == ns'
    NoMangle nm == NoMangle nm' = nm == nm'
    _ == _ = False

  public export
  Eq ITy where
    MkTy _ _ n ty == MkTy _ _ n' ty' = n == n' && ty == ty'

  public export
  Eq Data where
    MkData _ n tc os dc == MkData _ n' tc' os' dc' =
      n == n' && tc == tc' && os == os' && dc == dc'
    MkLater _ n tc == MkLater _ n' tc' =
      n == n' && tc == tc'
    _ == _ = False

  public export
  Eq IField where
    MkIField _ c pi n e == MkIField _ c' pi' n' e' =
      c == c' && pi == pi' && n == n' && e == e'

  public export
  Eq Record where
    MkRecord _ n ps cn fs == MkRecord _ n' ps' cn' fs' =
      n == n' && ps == ps' && cn == cn' && fs == fs'

  public export
  Eq Decl where
    IClaim _ c v fos t == IClaim _ c' v' fos' t' =
      c == c' && v == v' && fos == fos' && t == t'
    IData _ v t d == IData _ v' t' d' =
      v == v' && t == t' && d == d'
    IDef _ n cs == IDef _ n' cs' =
      n == n' && cs == cs'
    IParameters _ ps ds == IParameters _ ps' ds' =
      ps == ps' && (assert_total $ ds == ds')
    IRecord _ ns v tr r == IRecord _ ns' v' tr' r' =
      ns == ns' && v == v' && tr == tr' && r == r'
    INamespace _ ns ds == INamespace _ ns' ds' =
      ns == ns' && (assert_total $ ds == ds')
    ITransform _ n f t == ITransform _ n' f' t' =
      n == n' && f == f' && t == t'
    IRunElabDecl _ e == IRunElabDecl _ e' = e == e'
    ILog p == ILog p' = p == p'
    IBuiltin _ t n == IBuiltin _ t' n' =
      t == t' && n == n'
    _ == _ = False

public export
Eq TTImp where
  IVar _ v == IVar _ v' = v == v'
  IPi _ c i n a r == IPi _ c' i' n' a' r' =
    c == c' && (assert_total $ i == i') && n == n' && a == a' && r == r'
  ILam _ c i n a r == ILam _ c' i' n' a' r' =
    c == c' && (assert_total $ i == i') && n == n' && a == a' && r == r'
  ILet _ _ c n ty val s == ILet _ _ c' n' ty' val' s' =
    c == c' && n == n' && ty == ty' && val == val' && s == s'
  ICase _ t ty cs == ICase _ t' ty' cs'
    = t == t' && ty == ty' && (assert_total $ cs == cs')
  ILocal _ ds e == ILocal _ ds' e' =
    (assert_total $ ds == ds') && e == e'
  IUpdate _ fs t == IUpdate _ fs' t' =
    (assert_total $ fs == fs') && t == t'

  IApp _ f x == IApp _ f' x' = f == f' && x == x'
  INamedApp _ f n x == INamedApp _ f' n' x' =
    f == f' && n == n' && x == x'
  IAutoApp _ f x == IAutoApp _ f' x' = f == f' && x == x'
  IWithApp _ f x == IWithApp _ f' x' = f == f' && x == x'

  ISearch _ n == ISearch _ n' = n == n'
  IAlternative _ t as == IAlternative _ t' as' =
    (assert_total $ t == t') && (assert_total $ as == as')
  IRewrite _ p q == IRewrite _ p' q' =
    p == p' && q == q'

  IBindHere _ m t == IBindHere _ m' t' =
    m == m' && t == t'
  IBindVar _ s == IBindVar _ s' = s == s'
  IAs _ _ u n t == IAs _ _ u' n' t' =
    u == u' && n == n' && t == t'
  IMustUnify _ r t == IMustUnify _ r' t' =
    r == r' && t == t'

  IDelayed _ r t == IDelayed _ r' t' = r == r' && t == t'
  IDelay _ t == IDelay _ t' = t == t'
  IForce _ t == IForce _ t' = t == t'

  IQuote _ tm == IQuote _ tm' = tm == tm'
  IQuoteName _ n == IQuoteName _ n' = n == n'
  IQuoteDecl _ ds == IQuoteDecl _ ds' = assert_total $ ds == ds'
  IUnquote _ tm == IUnquote _ tm' = tm == tm'

  IPrimVal _ c == IPrimVal _ c' = c == c'
  IType _ == IType _ = True
  IHole _ s == IHole _ s' = s == s'

  Implicit _ b == Implicit _ b' = b == b'
  IWithUnambigNames _ ns t == IWithUnambigNames _ ns' t' =
    map snd ns == map snd ns' && t == t'

  _ == _ = False
