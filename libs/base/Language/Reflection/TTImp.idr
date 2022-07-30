module Language.Reflection.TTImp

import Data.Maybe
import Data.String
import public Language.Reflection.TT


%default total

-- Unchecked terms and declarations in the intermediate language
mutual
  public export
  data BindMode = PI Count | PATTERN | COVERAGE | NONE
  %name BindMode bm

  -- For as patterns matching linear arguments, select which side is
  -- consumed
  public export
  data UseSide = UseLeft | UseRight
  %name UseSide side

  public export
  data DotReason = NonLinearVar
                 | VarApplied
                 | NotConstructor
                 | ErasedArg
                 | UserDotted
                 | UnknownDot
                 | UnderAppliedCon
  %name DotReason dr

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
  %name TTImp s, t, u

  public export
  data IFieldUpdate : Type where
       ISetField : (path : List String) -> TTImp -> IFieldUpdate
       ISetFieldApp : (path : List String) -> TTImp -> IFieldUpdate

  %name IFieldUpdate upd

  public export
  data AltType : Type where
       FirstSuccess : AltType
       Unique : AltType
       UniqueDefault : TTImp -> AltType

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

  public export
  data ITy : Type where
       MkTy : FC -> (nameFC : FC) -> (n : Name) -> (ty : TTImp) -> ITy

  %name ITy sig

  public export
  data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors
       UniqueSearch : DataOpt -- auto implicit search must check result is unique
       External : DataOpt -- implemented externally
       NoNewtype : DataOpt -- don't apply newtype optimisation

  %name DataOpt dopt

  public export
  data Data : Type where
       MkData : FC -> (n : Name) -> (tycon : TTImp) ->
                (opts : List DataOpt) ->
                (datacons : List ITy) -> Data
       MkLater : FC -> (n : Name) -> (tycon : TTImp) -> Data

  %name Data dt

  public export
  data IField : Type where
       MkIField : FC -> Count -> PiInfo TTImp -> Name -> TTImp ->
                  IField

  %name IField fld

  public export
  data Record : Type where
       MkRecord : FC -> (n : Name) ->
                  (params : List (Name, Count, PiInfo TTImp, TTImp)) ->
                  (conName : Name) ->
                  (fields : List IField) ->
                  Record
  %name Record rec

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

  %name Clause cl

  public export
  data Decl : Type where
       IClaim : FC -> Count -> Visibility -> List FnOpt ->
                ITy -> Decl
       IData : FC -> Visibility -> Maybe TotalReq -> Data -> Decl
       IDef : FC -> Name -> (cls : List Clause) -> Decl
       IParameters : FC -> (params : List (Name, Count, PiInfo TTImp, TTImp)) ->
                     (decls : List Decl) -> Decl
       IRecord : FC ->
                 Maybe String -> -- nested namespace
                 Visibility -> Maybe TotalReq -> Record -> Decl
       INamespace : FC -> Namespace -> (decls : List Decl) -> Decl
       ITransform : FC -> Name -> TTImp -> TTImp -> Decl
       IRunElabDecl : FC -> TTImp -> Decl
       ILog : Maybe (List String, Nat) -> Decl
       IBuiltin : FC -> BuiltinType -> Name -> Decl

  %name Decl decl

public export
getFC : TTImp -> FC
getFC (IVar fc _)                = fc
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
mapTopmostFC : (FC -> FC) -> TTImp -> TTImp
mapTopmostFC fcf $ IVar fc a                = IVar (fcf fc) a
mapTopmostFC fcf $ IPi fc a b c d e         = IPi (fcf fc) a b c d e
mapTopmostFC fcf $ ILam fc a b c d e        = ILam (fcf fc) a b c d e
mapTopmostFC fcf $ ILet fc a b c d e f      = ILet (fcf fc) a b c d e f
mapTopmostFC fcf $ ICase fc a b c           = ICase (fcf fc) a b c
mapTopmostFC fcf $ ILocal fc a b            = ILocal (fcf fc) a b
mapTopmostFC fcf $ IUpdate fc a b           = IUpdate (fcf fc) a b
mapTopmostFC fcf $ IApp fc a b              = IApp (fcf fc) a b
mapTopmostFC fcf $ INamedApp fc a b c       = INamedApp (fcf fc) a b c
mapTopmostFC fcf $ IAutoApp fc a b          = IAutoApp (fcf fc) a b
mapTopmostFC fcf $ IWithApp fc a b          = IWithApp (fcf fc) a b
mapTopmostFC fcf $ ISearch fc a             = ISearch (fcf fc) a
mapTopmostFC fcf $ IAlternative fc a b      = IAlternative (fcf fc) a b
mapTopmostFC fcf $ IRewrite fc a b          = IRewrite (fcf fc) a b
mapTopmostFC fcf $ IBindHere fc a b         = IBindHere (fcf fc) a b
mapTopmostFC fcf $ IBindVar fc a            = IBindVar (fcf fc) a
mapTopmostFC fcf $ IAs fc a b c d           = IAs (fcf fc) a b c d
mapTopmostFC fcf $ IMustUnify fc a b        = IMustUnify (fcf fc) a b
mapTopmostFC fcf $ IDelayed fc a b          = IDelayed (fcf fc) a b
mapTopmostFC fcf $ IDelay fc a              = IDelay (fcf fc) a
mapTopmostFC fcf $ IForce fc a              = IForce (fcf fc) a
mapTopmostFC fcf $ IQuote fc a              = IQuote (fcf fc) a
mapTopmostFC fcf $ IQuoteName fc a          = IQuoteName (fcf fc) a
mapTopmostFC fcf $ IQuoteDecl fc a          = IQuoteDecl (fcf fc) a
mapTopmostFC fcf $ IUnquote fc a            = IUnquote (fcf fc) a
mapTopmostFC fcf $ IPrimVal fc a            = IPrimVal (fcf fc) a
mapTopmostFC fcf $ IType fc                 = IType (fcf fc)
mapTopmostFC fcf $ IHole fc a               = IHole (fcf fc) a
mapTopmostFC fcf $ Implicit fc a            = Implicit (fcf fc) a
mapTopmostFC fcf $ IWithUnambigNames fc a b = IWithUnambigNames (fcf fc) a b

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
Eq DataOpt where
  SearchBy ns == SearchBy ns' = ns == ns'
  NoHints == NoHints = True
  UniqueSearch == UniqueSearch = True
  External == External = True
  NoNewtype == NoNewtype = True
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

public export
data Mode = InDecl | InCase

mutual

  export
  Show IField where
    show (MkIField fc rig pinfo nm s) =
      showPiInfo {wrapExplicit=False} pinfo (showCount rig "\{show nm} : \{show s}")

  export
  Show Record where
    show (MkRecord fc n params conName fields)
      = unwords
      [ "record", show n
      , unwords (map (\ (nm, rig, pinfo, ty) =>
                       showPiInfo pinfo (showCount rig "\{show nm} : \{show ty}"))
                params)
      , "where"
      , "{"
      , "constructor", show conName, "; "
      , joinBy "; " (map show fields)
      , "}"
      ]

  export
  Show Data where
    show (MkData fc n tycon opts datacons) -- TODO: print opts
      = unwords
      [ "data", show n, ":", show tycon, "where"
      , "{", joinBy "; " (map show datacons), "}"
      ]
    show (MkLater fc n tycon) = unwords [ "data", show n, ":", show tycon ]

  export
  Show ITy where
    show (MkTy fc nameFC n ty) = "\{show n} : \{show ty}"

  export
  Show Decl where
    show (IClaim fc rig vis xs sig)
      = unwords [ show vis
                , showCount rig (show sig) ]
    show (IData fc vis treq dt)
      = unwords [ show vis
                , showTotalReq treq (show dt)
                ]
    show (IDef fc nm xs) = joinBy "; " (map (showClause InDecl) xs)
    show (IParameters fc params decls)
      = unwords
      [ "parameters"
      , unwords (map (\ (nm, rig, pinfo, ty) =>
                       showPiInfo pinfo (showCount rig "\{show nm} : \{show ty}"))
                params)
      , "{"
      , joinBy "; " (assert_total $ map show decls)
      , "}"
      ]
    show (IRecord fc x vis treq rec)
      = unwords [ show vis, showTotalReq treq (show rec) ]
    show (INamespace fc ns decls)
      = unwords
      [ "namespace", show ns
      , "{", joinBy "; " (assert_total $ map show decls), "}" ]
    show (ITransform fc nm s t) = #"%transform "\{show nm}" \{show s} = \{show t}"#
    show (IRunElabDecl fc s) = "%runElab \{show s}"
    show (ILog loglvl) = case loglvl of
      Nothing => "%logging off"
      Just ([], lvl) => "%logging \{show lvl}"
      Just (topic, lvl) => "%logging \{joinBy "." topic} \{show lvl}"
    show (IBuiltin fc bty nm) = "%builtin \{show bty} \{show nm}"

  export
  Show IFieldUpdate where
    show (ISetField path s) = "\{joinBy "->" path} := \{show s}"
    show (ISetFieldApp path s) = "\{joinBy "->" path} $= \{show s}"

  export
  showClause : Mode -> Clause -> String
  showClause mode (PatClause fc lhs rhs) = "\{show lhs} \{showSep mode} \{show rhs}" where
    showSep : Mode -> String
    showSep InDecl = "="
    showSep InCase = "=>"
  showClause mode (WithClause fc lhs rig wval prf flags cls) -- TODO print flags
      = unwords
      [ show lhs, "with"
      , showCount rig $ maybe id (\ nm => (++ " proof \{show nm}")) prf
                      $ showParens True (show wval)
      , "{", joinBy "; " (assert_total $ map (showClause mode) cls), "}"
      ]
  showClause mode (ImpossibleClause fc lhs) = "\{show lhs} impossible"

  collectPis : Count -> PiInfo TTImp -> SnocList Name -> TTImp -> TTImp -> (List Name, TTImp)
  collectPis rig pinfo xs argTy t@(IPi fc rig' pinfo' x argTy' retTy)
    = ifThenElse (rig == rig' && pinfo == pinfo' && argTy == argTy')
         (collectPis rig pinfo (xs :< fromMaybe (UN Underscore) x) argTy retTy)
         (xs <>> [], t)
  collectPis rig pinfo xs argTy t = (xs <>> [], t)

  showIApps : TTImp -> List String -> String
  showIApps (IApp _ f t) ts = showIApps f (assert_total (showPrec App t) :: ts)
  showIApps (IVar _ nm) [a,b] =
    if isOp nm then unwords [a, showPrefix False nm, b]
    else unwords [showPrefix True nm, a, b]
  showIApps f ts = unwords (show f :: ts)

  export
  Show TTImp where
    showPrec d (IVar fc nm) = showPrefix True nm
    showPrec d (IPi fc MW ExplicitArg Nothing argTy retTy)
      = showParens (d > Open) $ "\{showPrec Dollar argTy} -> \{show retTy}"
    showPrec d (IPi fc MW AutoImplicit Nothing argTy retTy)
      = showParens (d > Open) $ "\{showPrec Dollar argTy} => \{show retTy}"
    showPrec d (IPi fc rig pinfo x argTy retTy)
      = showParens (d > Open) $
          let (xs, retTy) = collectPis rig pinfo [<fromMaybe (UN Underscore) x] argTy retTy in
          assert_total (showPiInfo pinfo "\{showCount rig $ joinBy ", " (show <$> xs)} : \{show argTy}")
          ++ " -> \{assert_total $ show retTy}"
    showPrec d (ILam fc rig pinfo x argTy lamTy)
      = showParens (d > Open) $
          "\\ \{showCount rig $ show (fromMaybe (UN Underscore) x)} => \{show lamTy}"
    showPrec d (ILet fc lhsFC rig nm nTy nVal scope)
      = showParens (d > Open) $
          "let \{showCount rig (show nm)} : \{show nTy} = \{show nVal} in \{show scope}"
    showPrec d (ICase fc s ty xs)
      = showParens (d > Open) $
          unwords $ [ "case", show s ] ++ typeFor ty ++ [ "of", "{"
                    , joinBy "; " (assert_total $ map (showClause InCase) xs)
                    , "}"
                    ]
          where
            typeFor : TTImp -> List String
            typeFor $ Implicit _ False = []
            typeFor ty = [ "{-", ":", show ty, "-}" ]
    showPrec d (ILocal fc decls s)
      = showParens (d > Open) $
          unwords [ "let", joinBy "; " (assert_total $ map show decls)
                  , "in", show s
                  ]
    showPrec d (IUpdate fc upds s)
      = showParens (d > Open) $
          unwords [ "{", joinBy ", " $ assert_total (map show upds), "}"
                  , showPrec App s ]
    showPrec d (IApp fc f t)
      = showParens (d >= App) $ assert_total $ showIApps f [showPrec App t]
    showPrec d (INamedApp fc f nm t)
      = showParens (d >= App) $ "\{show f} {\{show nm} = \{show t}}"
    showPrec d (IAutoApp fc f t)
      = showParens (d >= App) $ "\{show f} @{\{show t}}"
    showPrec d (IWithApp fc f t)
      = showParens (d >= App) $ "\{show f} | \{showPrec App t}"
    showPrec d (ISearch fc depth) = "%search"
    showPrec d (IAlternative fc x xs) = "<\{show (length xs)} alts>"
    showPrec d (IRewrite fc s t)
      = showParens (d > Open) "rewrite \{show s} in \{show t}"
    showPrec d (IBindHere fc bm s) = showPrec d s
    showPrec d (IBindVar fc x) = x
    showPrec d (IAs fc nameFC side nm s)
      = "\{show nm}@\{showPrec App s}"
    showPrec d (IMustUnify fc dr s) = ".(\{show s})"
    showPrec d (IDelayed fc LInf s) = showCon d "Inf" $ assert_total $ showArg s
    showPrec d (IDelayed fc LLazy s) = showCon d "Lazy" $ assert_total $ showArg s
    showPrec d (IDelayed fc LUnknown s) = "({- unknown lazy -} \{showPrec Open s})"
    showPrec d (IDelay fc s) = showCon d "Delay" $ assert_total $ showArg s
    showPrec d (IForce fc s) = showCon d "Force" $ assert_total $ showArg s
    showPrec d (IQuote fc s) = "`(\{show s})"
    showPrec d (IQuoteName fc nm) = "`{\{show nm}}"
    showPrec d (IQuoteDecl fc xs) = "`[\{joinBy "; " (assert_total $ map show xs)}]"
    showPrec d (IUnquote fc s) = "~(\{show s})"
    showPrec d (IPrimVal fc c) = show c
    showPrec d (IType fc) = "Type"
    showPrec d (IHole fc str) = "?" ++ str
    showPrec d (Implicit fc b) = ifThenElse b "_" "?"
    showPrec d (IWithUnambigNames fc ns s) = case ns of
      [] => show s
      [(_,x)] => "with \{show x} \{show s}"
      _   => "with [\{joinBy ", " $ map (show . snd) ns}] \{show s}"

public export
data Argument a
  = Arg FC a
  | NamedArg FC Name a
  | AutoArg FC a

export
unArg : Argument a -> a
unArg (Arg _ x) = x
unArg (NamedArg _ _ x) = x
unArg (AutoArg _ x) = x

public export
data IsAppView : (FC, Name) -> SnocList (Argument TTImp) -> TTImp -> Type where
  AVVar : IsAppView (fc, t) [<] (IVar fc t)
  AVApp : IsAppView x ts f -> IsAppView x (ts :< Arg fc t) (IApp fc f t)
  AVNamedApp : IsAppView x ts f -> IsAppView x (ts :< NamedArg fc n t) (INamedApp fc f n t)
  AVAutoApp : IsAppView x ts f -> IsAppView x (ts :< AutoArg fc t) (IAutoApp fc f a)

public export
record AppView (t : TTImp) where
  constructor MkAppView
  head : (FC, Name)
  args : SnocList (Argument TTImp)
  0 isAppView : IsAppView head args t

export
appView : (t : TTImp) -> Maybe (AppView t)
appView (IVar fc f) = Just (MkAppView (fc, f) [<] AVVar)
appView (IApp fc f t) = do
  (MkAppView x ts prf) <- appView f
  pure (MkAppView x (ts :< Arg fc t) (AVApp prf))
appView (INamedApp fc f n t) = do
  (MkAppView x ts prf) <- appView f
  pure (MkAppView x (ts :< NamedArg fc n t) (AVNamedApp prf))
appView (IAutoApp fc f t) = do
  (MkAppView x ts prf) <- appView f
  pure (MkAppView x (ts :< AutoArg fc t) (AVAutoApp prf))
appView _ = Nothing

parameters (f : TTImp -> TTImp)

  export
  mapTTImp : TTImp -> TTImp

  export
  mapPiInfo : PiInfo TTImp -> PiInfo TTImp
  mapPiInfo ImplicitArg = ImplicitArg
  mapPiInfo ExplicitArg = ExplicitArg
  mapPiInfo AutoImplicit = AutoImplicit
  mapPiInfo (DefImplicit t) = DefImplicit (mapTTImp t)

  export
  mapClause : Clause -> Clause
  mapClause (PatClause fc lhs rhs) = PatClause fc (mapTTImp lhs) (mapTTImp rhs)
  mapClause (WithClause fc lhs rig wval prf flags cls)
    = WithClause fc (mapTTImp lhs) rig (mapTTImp wval) prf flags (assert_total $ map mapClause cls)
  mapClause (ImpossibleClause fc lhs) = ImpossibleClause fc (mapTTImp lhs)

  export
  mapITy : ITy -> ITy
  mapITy (MkTy fc nameFC n ty) = MkTy fc nameFC n (mapTTImp ty)

  export
  mapFnOpt : FnOpt -> FnOpt
  mapFnOpt Inline = Inline
  mapFnOpt NoInline = NoInline
  mapFnOpt Deprecate = Deprecate
  mapFnOpt TCInline = TCInline
  mapFnOpt (Hint b) = Hint b
  mapFnOpt (GlobalHint b) = GlobalHint b
  mapFnOpt ExternFn = ExternFn
  mapFnOpt (ForeignFn ts) = ForeignFn (map mapTTImp ts)
  mapFnOpt (ForeignExport ts) = ForeignExport (map mapTTImp ts)
  mapFnOpt Invertible = Invertible
  mapFnOpt (Totality treq) = Totality treq
  mapFnOpt Macro = Macro
  mapFnOpt (SpecArgs ns) = SpecArgs ns

  export
  mapData : Data -> Data
  mapData (MkData fc n tycon opts datacons)
    = MkData fc n (mapTTImp tycon) opts (map mapITy datacons)
  mapData (MkLater fc n tycon) = MkLater fc n (mapTTImp tycon)

  export
  mapIField : IField -> IField
  mapIField (MkIField fc rig pinfo n t) = MkIField fc rig (mapPiInfo pinfo) n (mapTTImp t)

  export
  mapRecord : Record -> Record
  mapRecord (MkRecord fc n params conName fields)
    = MkRecord fc n (map (map $ map $ bimap mapPiInfo mapTTImp) params) conName (map mapIField fields)

  export
  mapDecl : Decl -> Decl
  mapDecl (IClaim fc rig vis opts ty)
    = IClaim fc rig vis (map mapFnOpt opts) (mapITy ty)
  mapDecl (IData fc vis mtreq dat) = IData fc vis mtreq (mapData dat)
  mapDecl (IDef fc n cls) = IDef fc n (map mapClause cls)
  mapDecl (IParameters fc params xs) = IParameters fc params (assert_total $ map mapDecl xs)
  mapDecl (IRecord fc mstr x y rec) = IRecord fc mstr x y (mapRecord rec)
  mapDecl (INamespace fc mi xs) = INamespace fc mi (assert_total $ map mapDecl xs)
  mapDecl (ITransform fc n t u) = ITransform fc n (mapTTImp t) (mapTTImp u)
  mapDecl (IRunElabDecl fc t) = IRunElabDecl fc (mapTTImp t)
  mapDecl (ILog x) = ILog x
  mapDecl (IBuiltin fc x n) = IBuiltin fc x n

  export
  mapIFieldUpdate : IFieldUpdate -> IFieldUpdate
  mapIFieldUpdate (ISetField path t) = ISetField path (mapTTImp t)
  mapIFieldUpdate (ISetFieldApp path t) = ISetFieldApp path (mapTTImp t)

  export
  mapAltType : AltType -> AltType
  mapAltType FirstSuccess = FirstSuccess
  mapAltType Unique = Unique
  mapAltType (UniqueDefault t) = UniqueDefault (mapTTImp t)

  mapTTImp t@(IVar _ _) = f t
  mapTTImp (IPi fc rig pinfo x argTy retTy)
    = f $ IPi fc rig (mapPiInfo pinfo) x (mapTTImp argTy) (mapTTImp retTy)
  mapTTImp (ILam fc rig pinfo x argTy lamTy)
    = f $ ILam fc rig (mapPiInfo pinfo) x (mapTTImp argTy) (mapTTImp lamTy)
  mapTTImp (ILet fc lhsFC rig n nTy nVal scope)
    = f $ ILet fc lhsFC rig n (mapTTImp nTy) (mapTTImp nVal) (mapTTImp scope)
  mapTTImp (ICase fc t ty cls)
    = f $ ICase fc (mapTTImp t) (mapTTImp ty) (assert_total $ map mapClause cls)
  mapTTImp (ILocal fc xs t)
    = f $ ILocal fc (assert_total $ map mapDecl xs) (mapTTImp t)
  mapTTImp (IUpdate fc upds t) = f $ IUpdate fc (assert_total map mapIFieldUpdate upds) (mapTTImp t)
  mapTTImp (IApp fc t u) = f $ IApp fc (mapTTImp t) (mapTTImp u)
  mapTTImp (IAutoApp fc t u) = f $ IAutoApp fc (mapTTImp t) (mapTTImp u)
  mapTTImp (INamedApp fc t n u) = f $ INamedApp fc (mapTTImp t) n (mapTTImp u)
  mapTTImp (IWithApp fc t u) = f $ IWithApp fc (mapTTImp t) (mapTTImp u)
  mapTTImp (ISearch fc depth) = f $ ISearch fc depth
  mapTTImp (IAlternative fc alt ts) = f $ IAlternative fc (mapAltType alt) (assert_total map mapTTImp ts)
  mapTTImp (IRewrite fc t u) = f $ IRewrite fc (mapTTImp t) (mapTTImp u)
  mapTTImp (IBindHere fc bm t) = f $ IBindHere fc bm (mapTTImp t)
  mapTTImp (IBindVar fc str) = f $ IBindVar fc str
  mapTTImp (IAs fc nameFC side n t) = f $ IAs fc nameFC side n (mapTTImp t)
  mapTTImp (IMustUnify fc x t) = f $ IMustUnify fc x (mapTTImp t)
  mapTTImp (IDelayed fc lz t) = f $ IDelayed fc lz (mapTTImp t)
  mapTTImp (IDelay fc t) = f $ IDelay fc (mapTTImp t)
  mapTTImp (IForce fc t) = f $ IForce fc (mapTTImp t)
  mapTTImp (IQuote fc t) = f $ IQuote fc (mapTTImp t)
  mapTTImp (IQuoteName fc n) = f $ IQuoteName fc n
  mapTTImp (IQuoteDecl fc xs) = f $ IQuoteDecl fc (assert_total $ map mapDecl xs)
  mapTTImp (IUnquote fc t) = f $ IUnquote fc (mapTTImp t)
  mapTTImp (IPrimVal fc c) = f $ IPrimVal fc c
  mapTTImp (IType fc) = f $ IType fc
  mapTTImp (IHole fc str) = f $ IHole fc str
  mapTTImp (Implicit fc bindIfUnsolved) = f $ Implicit fc bindIfUnsolved
  mapTTImp (IWithUnambigNames fc xs t) = f $ IWithUnambigNames fc xs (mapTTImp t)

parameters {0 m : Type -> Type} {auto mon : Monad m} (f : TTImp -> m TTImp)

  export
  mapMTTImp : TTImp -> m TTImp

  export
  mapMPiInfo : PiInfo TTImp -> m (PiInfo TTImp)
  mapMPiInfo ImplicitArg = pure ImplicitArg
  mapMPiInfo ExplicitArg = pure ExplicitArg
  mapMPiInfo AutoImplicit = pure AutoImplicit
  mapMPiInfo (DefImplicit t) = DefImplicit <$> mapMTTImp t

  export
  mapMClause : Clause -> m Clause
  mapMClause (PatClause fc lhs rhs) = PatClause fc <$> mapMTTImp lhs <*> mapMTTImp rhs
  mapMClause (WithClause fc lhs rig wval prf flags cls)
    = WithClause fc
    <$> mapMTTImp lhs
    <*> pure rig
    <*> mapMTTImp wval
    <*> pure prf
    <*> pure flags
    <*> assert_total (traverse mapMClause cls)
  mapMClause (ImpossibleClause fc lhs) = ImpossibleClause fc <$> mapMTTImp lhs

  export
  mapMITy : ITy -> m ITy
  mapMITy (MkTy fc nameFC n ty) = MkTy fc nameFC n <$> mapMTTImp ty

  export
  mapMFnOpt : FnOpt -> m FnOpt
  mapMFnOpt Inline = pure Inline
  mapMFnOpt NoInline = pure NoInline
  mapMFnOpt Deprecate = pure Deprecate
  mapMFnOpt TCInline = pure TCInline
  mapMFnOpt (Hint b) = pure (Hint b)
  mapMFnOpt (GlobalHint b) = pure (GlobalHint b)
  mapMFnOpt ExternFn = pure ExternFn
  mapMFnOpt (ForeignFn ts) = ForeignFn <$> traverse mapMTTImp ts
  mapMFnOpt (ForeignExport ts) = ForeignExport <$> traverse mapMTTImp ts
  mapMFnOpt Invertible = pure Invertible
  mapMFnOpt (Totality treq) = pure (Totality treq)
  mapMFnOpt Macro = pure Macro
  mapMFnOpt (SpecArgs ns) = pure (SpecArgs ns)

  export
  mapMData : Data -> m Data
  mapMData (MkData fc n tycon opts datacons)
    = MkData fc n <$> mapMTTImp tycon <*> pure opts <*> traverse mapMITy datacons
  mapMData (MkLater fc n tycon) = MkLater fc n <$> mapMTTImp tycon

  export
  mapMIField : IField -> m IField
  mapMIField (MkIField fc rig pinfo n t)
   = MkIField fc rig <$> mapMPiInfo pinfo <*> pure n <*> mapMTTImp t

  export
  mapMRecord : Record -> m Record
  mapMRecord (MkRecord fc n params conName fields)
    = MkRecord fc n
    <$> traverse (bitraverse pure $ bitraverse pure $ bitraverse mapMPiInfo mapMTTImp) params
    <*> pure conName
    <*> traverse mapMIField fields

  export
  mapMDecl : Decl -> m Decl
  mapMDecl (IClaim fc rig vis opts ty)
    = IClaim fc rig vis <$> traverse mapMFnOpt opts <*> mapMITy ty
  mapMDecl (IData fc vis mtreq dat) = IData fc vis mtreq <$> mapMData dat
  mapMDecl (IDef fc n cls) = IDef fc n <$> traverse mapMClause cls
  mapMDecl (IParameters fc params xs) = IParameters fc params <$> assert_total (traverse mapMDecl xs)
  mapMDecl (IRecord fc mstr x y rec) = IRecord fc mstr x y <$> mapMRecord rec
  mapMDecl (INamespace fc mi xs) = INamespace fc mi <$> assert_total (traverse mapMDecl xs)
  mapMDecl (ITransform fc n t u) = ITransform fc n <$> mapMTTImp t <*> mapMTTImp u
  mapMDecl (IRunElabDecl fc t) = IRunElabDecl fc <$> mapMTTImp t
  mapMDecl (ILog x) = pure (ILog x)
  mapMDecl (IBuiltin fc x n) = pure (IBuiltin fc x n)

  export
  mapMIFieldUpdate : IFieldUpdate -> m IFieldUpdate
  mapMIFieldUpdate (ISetField path t) = ISetField path <$> mapMTTImp t
  mapMIFieldUpdate (ISetFieldApp path t) = ISetFieldApp path <$> mapMTTImp t

  export
  mapMAltType : AltType -> m AltType
  mapMAltType FirstSuccess = pure FirstSuccess
  mapMAltType Unique = pure Unique
  mapMAltType (UniqueDefault t) = UniqueDefault <$> mapMTTImp t

  mapMTTImp t@(IVar _ _) = f t
  mapMTTImp (IPi fc rig pinfo x argTy retTy)
    = f =<< IPi fc rig <$> mapMPiInfo pinfo <*> pure x <*> mapMTTImp argTy <*> mapMTTImp retTy
  mapMTTImp (ILam fc rig pinfo x argTy lamTy)
    = f =<< ILam fc rig <$> mapMPiInfo pinfo <*> pure x <*> mapMTTImp argTy <*> mapMTTImp lamTy
  mapMTTImp (ILet fc lhsFC rig n nTy nVal scope)
    = f =<< ILet fc lhsFC rig n <$> mapMTTImp nTy <*> mapMTTImp nVal <*> mapMTTImp scope
  mapMTTImp (ICase fc t ty cls)
    = f =<< ICase fc <$> mapMTTImp t <*> mapMTTImp ty <*> assert_total (traverse mapMClause cls)
  mapMTTImp (ILocal fc xs t)
    = f =<< ILocal fc <$> assert_total (traverse mapMDecl xs) <*> mapMTTImp t
  mapMTTImp (IUpdate fc upds t)
    = f =<< IUpdate fc <$> assert_total (traverse mapMIFieldUpdate upds) <*> mapMTTImp t
  mapMTTImp (IApp fc t u)
    = f =<< IApp fc <$> mapMTTImp t <*> mapMTTImp u
  mapMTTImp (IAutoApp fc t u)
    = f =<< IAutoApp fc <$> mapMTTImp t <*> mapMTTImp u
  mapMTTImp (INamedApp fc t n u)
    = f =<< INamedApp fc <$> mapMTTImp t <*> pure n <*> mapMTTImp u
  mapMTTImp (IWithApp fc t u) = f =<< IWithApp fc <$> mapMTTImp t <*> mapMTTImp u
  mapMTTImp (ISearch fc depth) = f (ISearch fc depth)
  mapMTTImp (IAlternative fc alt ts)
    = f =<< IAlternative fc <$> mapMAltType alt <*> assert_total (traverse mapMTTImp ts)
  mapMTTImp (IRewrite fc t u) = f =<< IRewrite fc <$> mapMTTImp t <*> mapMTTImp u
  mapMTTImp (IBindHere fc bm t) = f =<< IBindHere fc bm <$> mapMTTImp t
  mapMTTImp (IBindVar fc str) = f (IBindVar fc str)
  mapMTTImp (IAs fc nameFC side n t) = f =<< IAs fc nameFC side n <$> mapMTTImp t
  mapMTTImp (IMustUnify fc x t) = f =<< IMustUnify fc x <$> mapMTTImp t
  mapMTTImp (IDelayed fc lz t) = f =<< IDelayed fc lz <$> mapMTTImp t
  mapMTTImp (IDelay fc t) = f =<< IDelay fc <$> mapMTTImp t
  mapMTTImp (IForce fc t) = f =<< IForce fc <$> mapMTTImp t
  mapMTTImp (IQuote fc t) = f =<< IQuote fc <$> mapMTTImp t
  mapMTTImp (IQuoteName fc n) = f (IQuoteName fc n)
  mapMTTImp (IQuoteDecl fc xs) = f =<< IQuoteDecl fc <$> assert_total (traverse mapMDecl xs)
  mapMTTImp (IUnquote fc t) = f =<< IUnquote fc <$> mapMTTImp t
  mapMTTImp (IPrimVal fc c) = f (IPrimVal fc c)
  mapMTTImp (IType fc) = f (IType fc)
  mapMTTImp (IHole fc str) = f (IHole fc str)
  mapMTTImp (Implicit fc bindIfUnsolved) = f (Implicit fc bindIfUnsolved)
  mapMTTImp (IWithUnambigNames fc xs t) = f =<< IWithUnambigNames fc xs <$> mapMTTImp t
