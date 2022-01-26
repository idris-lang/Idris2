module TTImp.TTImp

import Core.Binary
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Options
import Core.Options.Log
import Core.TT
import Core.TTC
import Core.Value

import Data.List
import Data.Maybe

%default covering

-- Information about names in nested blocks
public export
record NestedNames (vars : List Name) where
  constructor MkNested
  -- A map from names to the decorated version of the name, and the new name
  -- applied to its enclosing environment
  -- Takes the location and name type, because we don't know them until we
  -- elaborate the name at the point of use
  names : List (Name, (Maybe Name,  -- new name if there is one
                       List (Var vars), -- names used from the environment
                       FC -> NameType -> Term vars))

export
Weaken NestedNames where
  weaken (MkNested ns) = MkNested (map wknName ns)
    where
      wknName : (Name, (Maybe Name, List (Var vars), FC -> NameType -> Term vars)) ->
                (Name, (Maybe Name, List (Var (n :: vars)), FC -> NameType -> Term (n :: vars)))
      wknName (n, (mn, vars, rep))
          = (n, (mn, map weaken vars, \fc, nt => weaken (rep fc nt)))

-- Unchecked terms, with implicit arguments
-- This is the raw, elaboratable form.
-- Higher level expressions (e.g. case, pattern matching let, where blocks,
-- do notation, etc, should elaborate via this, perhaps in some local
-- context).
public export
data BindMode = PI RigCount | PATTERN | COVERAGE | NONE

mutual

  public export
  RawImp : Type
  RawImp = RawImp' Name

  public export
  IRawImp : Type
  IRawImp = RawImp' KindedName

  public export
  data RawImp' : Type -> Type where
       IVar : FC -> nm -> RawImp' nm
       IPi : FC -> RigCount -> PiInfo (RawImp' nm) -> Maybe Name ->
             (argTy : RawImp' nm) -> (retTy : RawImp' nm) -> RawImp' nm
       ILam : FC -> RigCount -> PiInfo (RawImp' nm) -> Maybe Name ->
              (argTy : RawImp' nm) -> (lamTy : RawImp' nm) -> RawImp' nm
       ILet : FC -> (lhsFC : FC) -> RigCount -> Name ->
              (nTy : RawImp' nm) -> (nVal : RawImp' nm) ->
              (scope : RawImp' nm) -> RawImp' nm
       ICase : FC -> RawImp' nm -> (ty : RawImp' nm) ->
               List (ImpClause' nm) -> RawImp' nm
       ILocal : FC -> List (ImpDecl' nm) -> RawImp' nm -> RawImp' nm
       -- Local definitions made elsewhere, but that we're pushing
       -- into a case branch as nested names.
       -- An appearance of 'uname' maps to an application of
       -- 'internalName' to 'args'.
       ICaseLocal : FC -> (uname : Name) ->
                    (internalName : Name) ->
                    (args : List Name) -> RawImp' nm -> RawImp' nm

       IUpdate : FC -> List (IFieldUpdate' nm) -> RawImp' nm -> RawImp' nm

       IApp : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm
       IAutoApp : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm
       INamedApp : FC -> RawImp' nm -> Name -> RawImp' nm -> RawImp' nm
       IWithApp : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm

       ISearch : FC -> (depth : Nat) -> RawImp' nm
       IAlternative : FC -> AltType' nm -> List (RawImp' nm) -> RawImp' nm
       IRewrite : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm
       ICoerced : FC -> RawImp' nm -> RawImp' nm

       -- Any implicit bindings in the scope should be bound here, using
       -- the given binder
       IBindHere : FC -> BindMode -> RawImp' nm -> RawImp' nm
       -- A name which should be implicitly bound
       IBindVar : FC -> String -> RawImp' nm
       -- An 'as' pattern, valid on the LHS of a clause only
       IAs : FC -> (nameFC : FC) -> UseSide -> Name -> RawImp' nm -> RawImp' nm
       -- A 'dot' pattern, i.e. one which must also have the given value
       -- by unification
       IMustUnify : FC -> DotReason -> RawImp' nm -> RawImp' nm

       -- Laziness annotations
       IDelayed : FC -> LazyReason -> RawImp' nm -> RawImp' nm -- the type
       IDelay : FC -> RawImp' nm -> RawImp' nm -- delay constructor
       IForce : FC -> RawImp' nm -> RawImp' nm

       -- Quasiquoting
       IQuote : FC -> RawImp' nm -> RawImp' nm
       IQuoteName : FC -> Name -> RawImp' nm
       IQuoteDecl : FC -> List (ImpDecl' nm) -> RawImp' nm
       IUnquote : FC -> RawImp' nm -> RawImp' nm
       IRunElab : FC -> RawImp' nm -> RawImp' nm

       IPrimVal : FC -> (c : Constant) -> RawImp' nm
       IType : FC -> RawImp' nm
       IHole : FC -> String -> RawImp' nm

       IUnifyLog : FC -> LogLevel -> RawImp' nm -> RawImp' nm
       -- An implicit value, solved by unification, but which will also be
       -- bound (either as a pattern variable or a type variable) if unsolved
       -- at the end of elaborator
       Implicit : FC -> (bindIfUnsolved : Bool) -> RawImp' nm

       -- with-disambiguation
       IWithUnambigNames : FC -> List Name -> RawImp' nm -> RawImp' nm

  public export
  IFieldUpdate : Type
  IFieldUpdate = IFieldUpdate' Name

  public export
  data IFieldUpdate' : Type -> Type where
       ISetField : (path : List String) -> RawImp' nm -> IFieldUpdate' nm
       ISetFieldApp : (path : List String) -> RawImp' nm -> IFieldUpdate' nm

  public export
  AltType : Type
  AltType = AltType' Name

  public export
  data AltType' : Type -> Type where
       FirstSuccess : AltType' nm
       Unique : AltType' nm
       UniqueDefault : RawImp' nm -> AltType' nm

  export
  covering
  Show nm => Show (RawImp' nm) where
      show (IVar fc n) = show n
      show (IPi fc c p n arg ret)
         = "(%pi " ++ show c ++ " " ++ show p ++ " " ++
           showPrec App n ++ " " ++ show arg ++ " " ++ show ret ++ ")"
      show (ILam fc c p n arg sc)
         = "(%lam " ++ show c ++ " " ++ show p ++ " " ++
           showPrec App n ++ " " ++ show arg ++ " " ++ show sc ++ ")"
      show (ILet fc lhsFC c n ty val sc)
         = "(%let " ++ show c ++ " " ++ " " ++ show n ++ " " ++ show ty ++
           " " ++ show val ++ " " ++ show sc ++ ")"
      show (ICase _ scr scrty alts)
         = "(%case (" ++ show scr ++ " : " ++ show scrty ++ ") " ++ show alts ++ ")"
      show (ILocal _ def scope)
         = "(%local (" ++ show def ++ ") " ++ show scope ++ ")"
      show (ICaseLocal _ uname iname args sc)
         = "(%caselocal (" ++ show uname ++ " " ++ show iname
               ++ " " ++ show args ++ ") " ++ show sc ++ ")"
      show (IUpdate _ flds rec)
         = "(%record " ++ showSep ", " (map show flds) ++ " " ++ show rec ++ ")"
      show (IApp fc f a)
         = "(" ++ show f ++ " " ++ show a ++ ")"
      show (INamedApp fc f n a)
         = "(" ++ show f ++ " [" ++ show n ++ " = " ++ show a ++ "])"
      show (IAutoApp fc f a)
         = "(" ++ show f ++ " [" ++ show a ++ "])"
      show (IWithApp fc f a)
         = "(" ++ show f ++ " | " ++ show a ++ ")"
      show (ISearch fc d)
         = "%search"
      show (IAlternative fc ty alts)
         = "(|" ++ showSep "," (map show alts) ++ "|)"
      show (IRewrite _ rule tm)
         = "(%rewrite (" ++ show rule ++ ") (" ++ show tm ++ "))"
      show (ICoerced _ tm) = "(%coerced " ++ show tm ++ ")"

      show (IBindHere fc b sc)
         = "(%bindhere " ++ show sc ++ ")"
      show (IBindVar fc n) = "$" ++ n
      show (IAs fc _ _ n tm) = show n ++ "@(" ++ show tm ++ ")"
      show (IMustUnify fc r tm) = ".(" ++ show tm ++ ")"
      show (IDelayed fc r tm) = "(%delayed " ++ show tm ++ ")"
      show (IDelay fc tm) = "(%delay " ++ show tm ++ ")"
      show (IForce fc tm) = "(%force " ++ show tm ++ ")"
      show (IQuote fc tm) = "(%quote " ++ show tm ++ ")"
      show (IQuoteName fc tm) = "(%quotename " ++ show tm ++ ")"
      show (IQuoteDecl fc tm) = "(%quotedecl " ++ show tm ++ ")"
      show (IUnquote fc tm) = "(%unquote " ++ show tm ++ ")"
      show (IRunElab fc tm) = "(%runelab " ++ show tm ++ ")"
      show (IPrimVal fc c) = show c
      show (IHole _ x) = "?" ++ x
      show (IUnifyLog _ lvl x) = "(%logging " ++ show lvl ++ " " ++ show x ++ ")"
      show (IType fc) = "%type"
      show (Implicit fc True) = "_"
      show (Implicit fc False) = "?"
      show (IWithUnambigNames fc ns rhs) = "(%with " ++ show ns ++ " " ++ show rhs ++ ")"

  export
  covering
  Show nm => Show (IFieldUpdate' nm) where
    show (ISetField p val) = showSep "->" p ++ " = " ++ show val
    show (ISetFieldApp p val) = showSep "->" p ++ " $= " ++ show val

  public export
  FnOpt : Type
  FnOpt = FnOpt' Name

  public export
  data FnOpt' : Type -> Type where
       Inline : FnOpt' nm
       NoInline : FnOpt' nm
       ||| Mark a function as deprecated.
       Deprecate : FnOpt' nm
       TCInline : FnOpt' nm
       -- Flag means the hint is a direct hint, not a function which might
       -- find the result (e.g. chasing parent interface dictionaries)
       Hint : Bool -> FnOpt' nm
       -- Flag means to use as a default if all else fails
       GlobalHint : Bool -> FnOpt' nm
       ExternFn : FnOpt' nm
       -- Defined externally, list calling conventions
       ForeignFn : List (RawImp' nm) -> FnOpt' nm
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt' nm
       Totality : TotalReq -> FnOpt' nm
       Macro : FnOpt' nm
       SpecArgs : List Name -> FnOpt' nm
       NoMangle : Maybe NoMangleDirective -> FnOpt' nm

  public export
  isTotalityReq : FnOpt' nm -> Bool
  isTotalityReq (Totality _) = True
  isTotalityReq _ = False

  export
  Show NoMangleDirective where
    show (CommonName name) = "\"\{name}\""
    show (BackendNames ns) = showSep " " (map (\(b, n) => "\"\{b}:\{n}\"") ns)

  export
  covering
  Show nm => Show (FnOpt' nm) where
    show Inline = "%inline"
    show NoInline = "%noinline"
    show Deprecate = "%deprecate"
    show TCInline = "%tcinline"
    show (Hint t) = "%hint " ++ show t
    show (GlobalHint t) = "%globalhint " ++ show t
    show ExternFn = "%extern"
    show (ForeignFn cs) = "%foreign " ++ showSep " " (map show cs)
    show Invertible = "%invertible"
    show (Totality Total) = "total"
    show (Totality CoveringOnly) = "covering"
    show (Totality PartialOK) = "partial"
    show Macro = "%macro"
    show (SpecArgs ns) = "%spec " ++ showSep " " (map show ns)
    show (NoMangle Nothing) = "%nomangle"
    show (NoMangle (Just ns)) = "%nomangle \{show ns}"

  export
  Eq NoMangleDirective where
    CommonName x == CommonName y = x == y
    BackendNames xs == BackendNames ys = xs == ys
    _ == _ = False

  export
  Eq FnOpt where
    Inline == Inline = True
    NoInline == NoInline = True
    Deprecate == Deprecate = True
    TCInline == TCInline = True
    (Hint x) == (Hint y) = x == y
    (GlobalHint x) == (GlobalHint y) = x == y
    ExternFn == ExternFn = True
    (ForeignFn xs) == (ForeignFn ys) = True -- xs == ys
    Invertible == Invertible = True
    (Totality tot_lhs) == (Totality tot_rhs) = tot_lhs == tot_rhs
    Macro == Macro = True
    (SpecArgs ns) == (SpecArgs ns') = ns == ns'
    (NoMangle x) == (NoMangle y) = x == y
    _ == _ = False

  public export
  ImpTy : Type
  ImpTy = ImpTy' Name

  public export
  data ImpTy' : Type -> Type where
       MkImpTy : FC -> (nameFC : FC) -> (n : Name) -> (ty : RawImp' nm) -> ImpTy' nm

  export
  covering
  Show nm => Show (ImpTy' nm) where
    show (MkImpTy fc _ n ty) = "(%claim " ++ show n ++ " " ++ show ty ++ ")"

  public export
  data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors
       UniqueSearch : DataOpt -- auto implicit search must check result is unique
       External : DataOpt -- implemented externally
       NoNewtype : DataOpt -- don't apply newtype optimisation

  export
  Eq DataOpt where
    (==) (SearchBy xs) (SearchBy ys) = xs == ys
    (==) NoHints NoHints = True
    (==) UniqueSearch UniqueSearch = True
    (==) External External = True
    (==) NoNewtype NoNewtype = True
    (==) _ _ = False

  public export
  ImpData : Type
  ImpData = ImpData' Name

  public export
  data ImpData' : Type -> Type where
       MkImpData : FC -> (n : Name) -> (tycon : RawImp' nm) ->
                   (opts : List DataOpt) ->
                   (datacons : List (ImpTy' nm)) -> ImpData' nm
       MkImpLater : FC -> (n : Name) -> (tycon : RawImp' nm) -> ImpData' nm

  export
  covering
  Show nm => Show (ImpData' nm) where
    show (MkImpData fc n tycon _ cons)
        = "(%data " ++ show n ++ " " ++ show tycon ++ " " ++
           show cons ++ ")"
    show (MkImpLater fc n tycon)
        = "(%datadecl " ++ show n ++ " " ++ show tycon ++ ")"

  public export
  IField : Type
  IField = IField' Name

  public export
  data IField' : Type -> Type where
       MkIField : FC -> RigCount -> PiInfo (RawImp' nm) -> Name -> RawImp' nm ->
                  IField' nm

  -- TODO: turn into a proper datatype
  public export
  ImpParameter' : Type -> Type
  ImpParameter' nm = (Name, RigCount, PiInfo (RawImp' nm), RawImp' nm)

  public export
  ImpRecord : Type
  ImpRecord = ImpRecord' Name

  public export
  data ImpRecord' : Type -> Type where
       MkImpRecord : FC -> (n : Name) ->
                     (params : List (ImpParameter' nm)) ->
                     (conName : Name) ->
                     (fields : List (IField' nm)) ->
                     ImpRecord' nm

  export
  covering
  Show nm => Show (IField' nm) where
    show (MkIField _ c Explicit n ty) = show n ++ " : " ++ show ty
    show (MkIField _ c _ n ty) = "{" ++ show n ++ " : " ++ show ty ++ "}"

  export
  covering
  Show nm => Show (ImpRecord' nm) where
    show (MkImpRecord _ n params con fields)
        = "record " ++ show n ++ " " ++ show params ++
          " " ++ show con ++ "\n\t" ++
          showSep "\n\t" (map show fields) ++ "\n"

  public export
  data WithFlag
         = Syntactic -- abstract syntactically, rather than by value

  export
  Eq WithFlag where
      Syntactic == Syntactic = True

  public export
  ImpClause : Type
  ImpClause = ImpClause' Name

  public export
  IImpClause : Type
  IImpClause = ImpClause' KindedName

  public export
  data ImpClause' : Type -> Type where
       PatClause : FC -> (lhs : RawImp' nm) -> (rhs : RawImp' nm) -> ImpClause' nm
       WithClause : FC -> (lhs : RawImp' nm) ->
                    (wval : RawImp' nm) -> (prf : Maybe Name) ->
                    (flags : List WithFlag) ->
                    List (ImpClause' nm) -> ImpClause' nm
       ImpossibleClause : FC -> (lhs : RawImp' nm) -> ImpClause' nm

  export
  covering
  Show nm => Show (ImpClause' nm) where
    show (PatClause fc lhs rhs)
       = show lhs ++ " = " ++ show rhs
    show (WithClause fc lhs wval prf flags block)
       = show lhs
       ++ " with " ++ show wval
       ++ maybe "" (\ nm => " proof " ++ show nm) prf
       ++ "\n\t" ++ show block
    show (ImpossibleClause fc lhs)
       = show lhs ++ " impossible"

  public export
  ImpDecl : Type
  ImpDecl = ImpDecl' Name

  public export
  data ImpDecl' : Type -> Type where
       IClaim : FC -> RigCount -> Visibility -> List (FnOpt' nm) ->
                ImpTy' nm -> ImpDecl' nm
       IData : FC -> Visibility -> Maybe TotalReq -> ImpData' nm -> ImpDecl' nm
       IDef : FC -> Name -> List (ImpClause' nm) -> ImpDecl' nm
       IParameters : FC ->
                     List (ImpParameter' nm) ->
                     List (ImpDecl' nm) -> ImpDecl' nm
       IRecord : FC ->
                 Maybe String -> -- nested namespace
                 Visibility -> Maybe TotalReq ->
                 ImpRecord' nm -> ImpDecl' nm
       INamespace : FC -> Namespace -> List (ImpDecl' nm) -> ImpDecl' nm
       ITransform : FC -> Name -> RawImp' nm -> RawImp' nm -> ImpDecl' nm
       IRunElabDecl : FC -> RawImp' nm -> ImpDecl' nm
       IPragma : List Name -> -- pragmas might define names that wouldn't
                       -- otherwise be spotted in 'definedInBlock' so they
                       -- can be flagged here.
                 ({vars : _} ->
                  NestedNames vars -> Env Term vars -> Core ()) ->
                 ImpDecl' nm
       ILog : Maybe (List String, Nat) -> ImpDecl' nm
       IBuiltin : FC -> BuiltinType -> Name -> ImpDecl' nm

  export
  covering
  Show nm => Show (ImpDecl' nm) where
    show (IClaim _ c _ opts ty) = show opts ++ " " ++ show c ++ " " ++ show ty
    show (IData _ _ _ d) = show d
    show (IDef _ n cs) = "(%def " ++ show n ++ " " ++ show cs ++ ")"
    show (IParameters _ ps ds)
        = "parameters " ++ show ps ++ "\n\t" ++
          showSep "\n\t" (assert_total $ map show ds)
    show (IRecord _ _ _ _ d) = show d
    show (INamespace _ ns decls)
        = "namespace " ++ show ns ++
          showSep "\n" (assert_total $ map show decls)
    show (ITransform _ n lhs rhs)
        = "%transform " ++ show n ++ " " ++ show lhs ++ " ==> " ++ show rhs
    show (IRunElabDecl _ tm)
        = "%runElab " ++ show tm
    show (IPragma _ _) = "[externally defined pragma]"
    show (ILog Nothing) = "%logging off"
    show (ILog (Just (topic, lvl))) = "%logging " ++ case topic of
      [] => show lvl
      _  => concat (intersperse "." topic) ++ " " ++ show lvl
    show (IBuiltin _ type name) = "%builtin " ++ show type ++ " " ++ show name


-- Extract the RawImp term from a FieldUpdate.
export
getFieldUpdateTerm : IFieldUpdate' nm -> RawImp' nm
getFieldUpdateTerm (ISetField    _ term) = term
getFieldUpdateTerm (ISetFieldApp _ term) = term


export
getFieldUpdatePath : IFieldUpdate' nm -> List String
getFieldUpdatePath (ISetField    path _) = path
getFieldUpdatePath (ISetFieldApp path _) = path


export
mapFieldUpdateTerm : (RawImp' nm -> RawImp' nm) -> IFieldUpdate' nm -> IFieldUpdate' nm
mapFieldUpdateTerm f (ISetField    x term) = ISetField    x (f term)
mapFieldUpdateTerm f (ISetFieldApp x term) = ISetFieldApp x (f term)


export
isIPrimVal : RawImp' nm -> Maybe Constant
isIPrimVal (IPrimVal _ c) = Just c
isIPrimVal _ = Nothing

-- REPL commands for TTImp interaction
public export
data ImpREPL : Type where
     Eval : RawImp -> ImpREPL
     Check : RawImp -> ImpREPL
     ProofSearch : Name -> ImpREPL
     ExprSearch : Name -> ImpREPL
     GenerateDef : Int -> Name -> ImpREPL
     Missing : Name -> ImpREPL
     CheckTotal : Name -> ImpREPL
     DebugInfo : Name -> ImpREPL
     Quit : ImpREPL

export
mapAltType : (RawImp' nm -> RawImp' nm) -> AltType' nm -> AltType' nm
mapAltType f (UniqueDefault x) = UniqueDefault (f x)
mapAltType _ u = u

export
lhsInCurrentNS : {auto c : Ref Ctxt Defs} ->
                 NestedNames vars -> RawImp -> Core RawImp
lhsInCurrentNS nest (IApp loc f a)
    = do f' <- lhsInCurrentNS nest f
         pure (IApp loc f' a)
lhsInCurrentNS nest (IAutoApp loc f a)
    = do f' <- lhsInCurrentNS nest f
         pure (IAutoApp loc f' a)
lhsInCurrentNS nest (INamedApp loc f n a)
    = do f' <- lhsInCurrentNS nest f
         pure (INamedApp loc f' n a)
lhsInCurrentNS nest (IWithApp loc f a)
    = do f' <- lhsInCurrentNS nest f
         pure (IWithApp loc f' a)
lhsInCurrentNS nest tm@(IVar loc (NS _ _)) = pure tm -- leave explicit NS alone
lhsInCurrentNS nest (IVar loc n)
    = case lookup n (names nest) of
           Nothing =>
              do n' <- inCurrentNS n
                 pure (IVar loc n')
           -- If it's one of the names in the current nested block, we'll
           -- be rewriting it during elaboration to be in the scope of the
           -- parent name.
           Just _ => pure (IVar loc n)
lhsInCurrentNS nest tm = pure tm

export
findIBinds : RawImp' nm -> List String
findIBinds (IPi fc rig p mn aty retty)
    = findIBinds aty ++ findIBinds retty
findIBinds (ILam fc rig p n aty sc)
    = findIBinds aty ++ findIBinds sc
findIBinds (IApp fc fn av)
    = findIBinds fn ++ findIBinds av
findIBinds (IAutoApp fc fn av)
    = findIBinds fn ++ findIBinds av
findIBinds (INamedApp _ fn _ av)
    = findIBinds fn ++ findIBinds av
findIBinds (IWithApp fc fn av)
    = findIBinds fn ++ findIBinds av
findIBinds (IAs fc _ _ (UN (Basic n)) pat)
    = n :: findIBinds pat
findIBinds (IAs fc _ _ n pat)
    = findIBinds pat
findIBinds (IMustUnify fc r pat)
    = findIBinds pat
findIBinds (IAlternative fc u alts)
    = concatMap findIBinds alts
findIBinds (IDelayed fc _ ty) = findIBinds ty
findIBinds (IDelay fc tm) = findIBinds tm
findIBinds (IForce fc tm) = findIBinds tm
findIBinds (IQuote fc tm) = findIBinds tm
findIBinds (IUnquote fc tm) = findIBinds tm
findIBinds (IRunElab fc tm) = findIBinds tm
findIBinds (IBindHere _ _ tm) = findIBinds tm
findIBinds (IBindVar _ n) = [n]
findIBinds (IUpdate fc updates tm)
    = findIBinds tm ++ concatMap (findIBinds . getFieldUpdateTerm) updates
-- We've skipped lambda, case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findIBinds tm = []

export
findImplicits : RawImp' nm -> List String
findImplicits (IPi fc rig p (Just (UN (Basic mn))) aty retty)
    = mn :: findImplicits aty ++ findImplicits retty
findImplicits (IPi fc rig p mn aty retty)
    = findImplicits aty ++ findImplicits retty
findImplicits (ILam fc rig p n aty sc)
    = findImplicits aty ++ findImplicits sc
findImplicits (IApp fc fn av)
    = findImplicits fn ++ findImplicits av
findImplicits (IAutoApp _ fn av)
    = findImplicits fn ++ findImplicits av
findImplicits (INamedApp _ fn _ av)
    = findImplicits fn ++ findImplicits av
findImplicits (IWithApp fc fn av)
    = findImplicits fn ++ findImplicits av
findImplicits (IAs fc _ _ n pat)
    = findImplicits pat
findImplicits (IMustUnify fc r pat)
    = findImplicits pat
findImplicits (IAlternative fc u alts)
    = concatMap findImplicits alts
findImplicits (IDelayed fc _ ty) = findImplicits ty
findImplicits (IDelay fc tm) = findImplicits tm
findImplicits (IForce fc tm) = findImplicits tm
findImplicits (IQuote fc tm) = findImplicits tm
findImplicits (IUnquote fc tm) = findImplicits tm
findImplicits (IRunElab fc tm) = findImplicits tm
findImplicits (IBindVar _ n) = [n]
findImplicits (IUpdate fc updates tm)
    = findImplicits tm ++ concatMap (findImplicits . getFieldUpdateTerm) updates
findImplicits tm = []

-- Update the lhs of a clause so that any implicits named in the type are
-- bound as @-patterns (unless they're already explicitly bound or appear as
-- IBindVar anywhere else in the pattern) so that they will be available on the
-- rhs
export
implicitsAs : {auto c : Ref Ctxt Defs} ->
              Int -> Defs ->
              (vars : List Name) ->
              RawImp -> Core RawImp
implicitsAs n defs ns tm
  = do let implicits = findIBinds tm
       log "declare.def.lhs.implicits" 30 $ "Found implicits: " ++ show implicits
       setAs (map Just (ns ++ map (UN . Basic) implicits)) [] tm
  where
    -- Takes the function application expression which is the lhs of a clause
    -- and decomposes it into the underlying function symbol and the variables
    -- bound by appearing as arguments, and then passes this onto `findImps`.
    -- More precisely, implicit and explicit arguments are recorded separately,
    -- into `is` and `es` respectively.
    setAs : List (Maybe Name) -> List (Maybe Name) -> RawImp -> Core RawImp
    setAs is es (IApp loc f a)
        = do f' <- setAs is (Nothing :: es) f
             pure $ IApp loc f' a
    setAs is es (IAutoApp loc f a)
        = do f' <- setAs (Nothing :: is) es f
             pure $ IAutoApp loc f' a
    setAs is es (INamedApp loc f n a)
        = do f' <- setAs (Just n :: is) (Just n :: es) f
             pure $ INamedApp loc f' n a
    setAs is es (IWithApp loc f a)
        = do f' <- setAs is es f
             pure $ IWithApp loc f' a
    setAs is es (IVar loc nm)
        -- #834 Use the (already) resolved name rather than the local one
        = case !(lookupTyExact (Resolved n) (gamma defs)) of
            Nothing =>
               do log "declare.def.lhs.implicits" 30 $
                    "Could not find variable " ++ show n
                  pure $ IVar loc nm
            Just ty =>
               do ty' <- nf defs [] ty
                  implicits <- findImps is es ns ty'
                  log "declare.def.lhs.implicits" 30 $
                    "\n  In the type of " ++ show n ++ ": " ++ show ty ++
                    "\n  Using locals: " ++ show ns ++
                    "\n  Found implicits: " ++ show implicits
                  pure $ impAs (virtualiseFC loc) implicits (IVar loc nm)
      where
        -- If there's an @{c} in the list of given implicits, that's the next
        -- autoimplicit, so don't rewrite the LHS and update the list of given
        -- implicits
        updateNs : Name -> List (Maybe Name) -> Maybe (List (Maybe Name))
        updateNs n (Nothing :: ns) = Just ns
        updateNs n (x :: ns)
            = if Just n == x
                 then Just ns -- found it
                 else do ns' <- updateNs n ns
                         pure (x :: ns')
        updateNs n [] = Nothing

        -- Finds the missing implicits which should be added to the lhs of the
        -- original pattern clause.
        --
        -- The first argument, `ns`, specifies which implicit variables alredy
        -- appear in the lhs, and therefore need not be added.
        -- The second argument, `es`, specifies which *explicit* variables appear
        -- in the lhs: this is used to determine when to stop searching for further
        -- implicits to add.
        findImps : List (Maybe Name) -> List (Maybe Name) ->
                   List Name -> NF [] ->
                   Core (List (Name, PiInfo RawImp))
        -- #834 When we are in a local definition, we have an explicit telescope
        -- corresponding to the variables bound in the parent function.
        -- So we first peel off all of the explicit quantifiers corresponding
        -- to these variables.
        findImps ns es (_ :: locals) (NBind fc x (Pi _ _ Explicit _) sc)
          = do body <- sc defs (toClosure defaultOpts [] (Erased fc False))
               findImps ns es locals body
               -- ^ TODO? check that name of the pi matches name of local?
        -- don't add implicits coming after explicits that aren't given
        findImps ns es [] (NBind fc x (Pi _ _ Explicit _) sc)
            = do body <- sc defs (toClosure defaultOpts [] (Erased fc False))
                 case es of
                   -- Explicits were skipped, therefore all explicits are given anyway
                   Just (UN Underscore) :: _ => findImps ns es [] body
                   -- Explicits weren't skipped, so we need to check
                   _ => case updateNs x es of
                          Nothing => pure [] -- explicit wasn't given
                          Just es' => findImps ns es' [] body
        -- if the implicit was given, skip it
        findImps ns es [] (NBind fc x (Pi _ _ AutoImplicit _) sc)
            = do body <- sc defs (toClosure defaultOpts [] (Erased fc False))
                 case updateNs x ns of
                   Nothing => -- didn't find explicit call
                      pure $ (x, AutoImplicit) :: !(findImps ns es [] body)
                   Just ns' => findImps ns' es [] body
        findImps ns es [] (NBind fc x (Pi _ _ p _) sc)
            = do body <- sc defs (toClosure defaultOpts [] (Erased fc False))
                 if Just x `elem` ns
                   then findImps ns es [] body
                   else pure $ (x, forgetDef p) :: !(findImps ns es [] body)
        findImps _ _ locals _
          = do log "declare.def.lhs.implicits" 50 $
                  "Giving up with the following locals left: " ++ show locals
               pure []

        impAs : FC -> List (Name, PiInfo RawImp) -> RawImp -> RawImp
        impAs loc' [] tm = tm
        impAs loc' ((nm@(UN (Basic n)), AutoImplicit) :: ns) tm
            = impAs loc' ns $
                 INamedApp loc' tm nm (IBindVar loc' n)

        impAs loc' ((n, Implicit) :: ns) tm
            = impAs loc' ns $
                 INamedApp loc' tm n
                     (IAs loc' EmptyFC UseLeft n (Implicit loc' True))

        impAs loc' ((n, DefImplicit t) :: ns) tm
            = impAs loc' ns $
                 INamedApp loc' tm n
                     (IAs loc' EmptyFC UseLeft n (Implicit loc' True))

        impAs loc' (_ :: ns) tm = impAs loc' ns tm
    setAs is es tm = pure tm

export
definedInBlock : Namespace -> -- namespace to resolve names
                 List ImpDecl -> List Name
definedInBlock ns decls =
    concatMap (defName ns) decls
  where
    getName : ImpTy -> Name
    getName (MkImpTy _ _ n _) = n

    getFieldName : IField -> Name
    getFieldName (MkIField _ _ _ n _) = n

    expandNS : Namespace -> Name -> Name
    expandNS ns n
       = if ns == emptyNS then n else case n of
           UN _ => NS ns n
           MN _ _ => NS ns n
           DN _ _ => NS ns n
           _ => n

    defName : Namespace -> ImpDecl -> List Name
    defName ns (IClaim _ _ _ _ ty) = [expandNS ns (getName ty)]
    defName ns (IData _ _ _ (MkImpData _ n _ _ cons))
        = expandNS ns n :: map (expandNS ns) (map getName cons)
    defName ns (IData _ _ _ (MkImpLater _ n _)) = [expandNS ns n]
    defName ns (IParameters _ _ pds) = concatMap (defName ns) pds
    defName ns (INamespace _ n nds) = concatMap (defName (ns <.> n)) nds
    defName ns (IRecord _ fldns _ _ (MkImpRecord _ n _ con flds))
        = expandNS ns con :: all
      where
        fldns' : Namespace
        fldns' = maybe ns (\ f => ns <.> mkNamespace f) fldns

        toRF : Name -> Name
        toRF (UN (Basic n)) = UN (Field n)
        toRF n = n

        fnsUN : List Name
        fnsUN = map getFieldName flds

        fnsRF : List Name
        fnsRF = map toRF fnsUN

        -- Depending on %prefix_record_projections,
        -- the record may or may not produce prefix projections (fnsUN).
        --
        -- However, since definedInBlock is pure, we can't check that flag
        -- (and it would also be wrong if %prefix_record_projections appears
        -- inside the parameter block)
        -- so let's just declare all of them and some may go unused.
        all : List Name
        all = expandNS ns n :: map (expandNS fldns') (fnsRF ++ fnsUN)

    defName ns (IPragma pns _) = map (expandNS ns) pns
    defName _ _ = []

export
isIVar : RawImp' nm -> Maybe (FC, nm)
isIVar (IVar fc v) = Just (fc, v)
isIVar _ = Nothing

export
isIBindVar : RawImp' nm -> Maybe (FC, String)
isIBindVar (IBindVar fc v) = Just (fc, v)
isIBindVar _ = Nothing

export
getFC : RawImp' nm -> FC
getFC (IVar x _) = x
getFC (IPi x _ _ _ _ _) = x
getFC (ILam x _ _ _ _ _) = x
getFC (ILet x _ _ _ _ _ _) = x
getFC (ICase x _ _ _) = x
getFC (ILocal x _ _) = x
getFC (ICaseLocal x _ _ _ _) = x
getFC (IUpdate x _ _) = x
getFC (IApp x _ _) = x
getFC (INamedApp x _ _ _) = x
getFC (IAutoApp x _ _) = x
getFC (IWithApp x _ _) = x
getFC (ISearch x _) = x
getFC (IAlternative x _ _) = x
getFC (IRewrite x _ _) = x
getFC (ICoerced x _) = x
getFC (IPrimVal x _) = x
getFC (IHole x _) = x
getFC (IUnifyLog x _ _) = x
getFC (IType x) = x
getFC (IBindVar x _) = x
getFC (IBindHere x _ _) = x
getFC (IMustUnify x _ _) = x
getFC (IDelayed x _ _) = x
getFC (IDelay x _) = x
getFC (IForce x _) = x
getFC (IQuote x _) = x
getFC (IQuoteName x _) = x
getFC (IQuoteDecl x _) = x
getFC (IUnquote x _) = x
getFC (IRunElab x _) = x
getFC (IAs x _ _ _ _) = x
getFC (Implicit x _) = x
getFC (IWithUnambigNames x _ _) = x

namespace ImpDecl

  public export
  getFC : ImpDecl' nm -> FC
  getFC (IClaim fc _ _ _ _) = fc
  getFC (IData fc _ _ _) = fc
  getFC (IDef fc _ _) = fc
  getFC (IParameters fc _ _) = fc
  getFC (IRecord fc _ _ _ _) = fc
  getFC (INamespace fc _ _) = fc
  getFC (ITransform fc _ _ _) = fc
  getFC (IRunElabDecl fc _) = fc
  getFC (IPragma _ _) = EmptyFC
  getFC (ILog _) = EmptyFC
  getFC (IBuiltin fc _ _) = fc

public export
data Arg' nm
   = Explicit FC (RawImp' nm)
   | Auto     FC (RawImp' nm)
   | Named    FC Name (RawImp' nm)

public export
Arg : Type
Arg = Arg' Name

public export
IArg : Type
IArg = Arg' KindedName

export
isExplicit : Arg' nm -> Maybe (FC, RawImp' nm)
isExplicit (Explicit fc t) = Just (fc, t)
isExplicit _ = Nothing

export
unIArg : Arg' nm -> RawImp' nm
unIArg (Explicit _ t) = t
unIArg (Auto _ t) = t
unIArg (Named _ _ t) = t

export
covering
Show nm => Show (Arg' nm) where
  show (Explicit fc t) = show t
  show (Auto fc t) = "@{" ++ show t ++ "}"
  show (Named fc n t) = "{" ++ show n ++ " = " ++ show t ++ "}"

export
getFnArgs : RawImp' nm -> List (Arg' nm) -> (RawImp' nm, List (Arg' nm))
getFnArgs (IApp fc f arg) args = getFnArgs f (Explicit fc arg :: args)
getFnArgs (INamedApp fc f n arg) args = getFnArgs f (Named fc n arg :: args)
getFnArgs (IAutoApp fc f arg) args = getFnArgs f (Auto fc arg :: args)
getFnArgs tm args = (tm, args)

-- TODO: merge these definitions
namespace Arg
  export
  apply : RawImp' nm -> List (Arg' nm) -> RawImp' nm
  apply f (Explicit fc a :: args) = apply (IApp fc f a) args
  apply f (Auto fc a :: args) = apply (IAutoApp fc f a) args
  apply f (Named fc n a :: args) = apply (INamedApp fc f n a) args
  apply f [] = f

export
apply : RawImp' nm -> List (RawImp' nm) -> RawImp' nm
apply f [] = f
apply f (x :: xs) =
  let fFC = getFC f in
  apply (IApp (fromMaybe fFC (mergeFC fFC (getFC x))) f x) xs

export
gapply : RawImp' nm -> List (Maybe Name, RawImp' nm) -> RawImp' nm
gapply f [] = f
gapply f (x :: xs) = gapply (uncurry (app f) x) xs where

  app : RawImp' nm -> Maybe Name -> RawImp' nm -> RawImp' nm
  app f Nothing x =  IApp (getFC f) f x
  app f (Just nm) x = INamedApp (getFC f) f nm x


export
getFn : RawImp' nm -> RawImp' nm
getFn (IApp _ f _) = getFn f
getFn (IWithApp _ f _) = getFn f
getFn (INamedApp _ f _ _) = getFn f
getFn (IAutoApp _ f _) = getFn f
getFn (IAs _ _ _ _ f) = getFn f
getFn (IMustUnify _ _ f) = getFn f
getFn f = f

-- Everything below is TTC instances

export
TTC BuiltinType where
    toBuf b BuiltinNatural = tag 0
    toBuf b NaturalToInteger = tag 1
    toBuf b IntegerToNatural = tag 2
    fromBuf b = case !getTag of
        0 => pure BuiltinNatural
        1 => pure NaturalToInteger
        2 => pure IntegerToNatural
        _ => corrupt "BuiltinType"

mutual
  export
  TTC RawImp where
    toBuf b (IVar fc n) = do tag 0; toBuf b fc; toBuf b n
    toBuf b (IPi fc r p n argTy retTy)
        = do tag 1; toBuf b fc; toBuf b r; toBuf b p; toBuf b n
             toBuf b argTy; toBuf b retTy
    toBuf b (ILam fc r p n argTy scope)
        = do tag 2; toBuf b fc; toBuf b r; toBuf b p; toBuf b n;
             toBuf b argTy; toBuf b scope
    toBuf b (ILet fc lhsFC r n nTy nVal scope)
        = do tag 3; toBuf b fc; toBuf b lhsFC; toBuf b r; toBuf b n;
             toBuf b nTy; toBuf b nVal; toBuf b scope
    toBuf b (ICase fc y ty xs)
        = do tag 4; toBuf b fc; toBuf b y; toBuf b ty; toBuf b xs
    toBuf b (ILocal fc xs sc)
        = do tag 5; toBuf b fc; toBuf b xs; toBuf b sc
    toBuf b (ICaseLocal fc _ _ _ sc)
        = toBuf b sc
    toBuf b (IUpdate fc fs rec)
        = do tag 6; toBuf b fc; toBuf b fs; toBuf b rec
    toBuf b (IApp fc fn arg)
        = do tag 7; toBuf b fc; toBuf b fn; toBuf b arg
    toBuf b (INamedApp fc fn y arg)
        = do tag 8; toBuf b fc; toBuf b fn; toBuf b y; toBuf b arg
    toBuf b (IWithApp fc fn arg)
        = do tag 9; toBuf b fc; toBuf b fn; toBuf b arg
    toBuf b (ISearch fc depth)
        = do tag 10; toBuf b fc; toBuf b depth
    toBuf b (IAlternative fc y xs)
        = do tag 11; toBuf b fc; toBuf b y; toBuf b xs
    toBuf b (IRewrite fc x y)
        = do tag 12; toBuf b fc; toBuf b x; toBuf b y
    toBuf b (ICoerced fc y)
        = do tag 13; toBuf b fc; toBuf b y

    toBuf b (IBindHere fc m y)
        = do tag 14; toBuf b fc; toBuf b m; toBuf b y
    toBuf b (IBindVar fc y)
        = do tag 15; toBuf b fc; toBuf b y
    toBuf b (IAs fc nameFC s y pattern)
        = do tag 16; toBuf b fc; toBuf b nameFC; toBuf b s; toBuf b y;
             toBuf b pattern
    toBuf b (IMustUnify fc r pattern)
        -- No need to record 'r', it's for type errors only
        = do tag 17; toBuf b fc; toBuf b pattern

    toBuf b (IDelayed fc r y)
        = do tag 18; toBuf b fc; toBuf b r; toBuf b y
    toBuf b (IDelay fc t)
        = do tag 19; toBuf b fc; toBuf b t
    toBuf b (IForce fc t)
        = do tag 20; toBuf b fc; toBuf b t

    toBuf b (IQuote fc t)
        = do tag 21; toBuf b fc; toBuf b t
    toBuf b (IQuoteName fc t)
        = do tag 22; toBuf b fc; toBuf b t
    toBuf b (IQuoteDecl fc t)
        = do tag 23; toBuf b fc; toBuf b t
    toBuf b (IUnquote fc t)
        = do tag 24; toBuf b fc; toBuf b t
    toBuf b (IRunElab fc t)
        = do tag 25; toBuf b fc; toBuf b t

    toBuf b (IPrimVal fc y)
        = do tag 26; toBuf b fc; toBuf b y
    toBuf b (IType fc)
        = do tag 27; toBuf b fc
    toBuf b (IHole fc y)
        = do tag 28; toBuf b fc; toBuf b y
    toBuf b (IUnifyLog fc lvl x) = toBuf b x

    toBuf b (Implicit fc i)
        = do tag 29; toBuf b fc; toBuf b i
    toBuf b (IWithUnambigNames fc ns rhs)
        = do tag 30; toBuf b ns; toBuf b rhs
    toBuf b (IAutoApp fc fn arg)
        = do tag 31; toBuf b fc; toBuf b fn; toBuf b arg

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; n <- fromBuf b;
                       pure (IVar fc n)
               1 => do fc <- fromBuf b;
                       r <- fromBuf b; p <- fromBuf b;
                       n <- fromBuf b
                       argTy <- fromBuf b; retTy <- fromBuf b
                       pure (IPi fc r p n argTy retTy)
               2 => do fc <- fromBuf b;
                       r <- fromBuf b; p <- fromBuf b; n <- fromBuf b
                       argTy <- fromBuf b; scope <- fromBuf b
                       pure (ILam fc r p n argTy scope)
               3 => do fc <- fromBuf b;
                       lhsFC <- fromBuf b;
                       r <- fromBuf b; n <- fromBuf b
                       nTy <- fromBuf b; nVal <- fromBuf b
                       scope <- fromBuf b
                       pure (ILet fc lhsFC r n nTy nVal scope)
               4 => do fc <- fromBuf b; y <- fromBuf b;
                       ty <- fromBuf b; xs <- fromBuf b
                       pure (ICase fc y ty xs)
               5 => do fc <- fromBuf b;
                       xs <- fromBuf b; sc <- fromBuf b
                       pure (ILocal fc xs sc)
               6 => do fc <- fromBuf b; fs <- fromBuf b
                       rec <- fromBuf b
                       pure (IUpdate fc fs rec)
               7 => do fc <- fromBuf b; fn <- fromBuf b
                       arg <- fromBuf b
                       pure (IApp fc fn arg)
               8 => do fc <- fromBuf b; fn <- fromBuf b
                       y <- fromBuf b; arg <- fromBuf b
                       pure (INamedApp fc fn y arg)
               9 => do fc <- fromBuf b; fn <- fromBuf b
                       arg <- fromBuf b
                       pure (IWithApp fc fn arg)
               10 => do fc <- fromBuf b; depth <- fromBuf b
                        pure (ISearch fc depth)
               11 => do fc <- fromBuf b; y <- fromBuf b
                        xs <- fromBuf b
                        pure (IAlternative fc y xs)
               12 => do fc <- fromBuf b; x <- fromBuf b; y <- fromBuf b
                        pure (IRewrite fc x y)
               13 => do fc <- fromBuf b; y <- fromBuf b
                        pure (ICoerced fc y)
               14 => do fc <- fromBuf b; m <- fromBuf b; y <- fromBuf b
                        pure (IBindHere fc m y)
               15 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IBindVar fc y)
               16 => do fc <- fromBuf b; nameFC <- fromBuf b
                        side <- fromBuf b;
                        y <- fromBuf b; pattern <- fromBuf b
                        pure (IAs fc nameFC side y pattern)
               17 => do fc <- fromBuf b
                        pattern <- fromBuf b
                        pure (IMustUnify fc UnknownDot pattern)

               18 => do fc <- fromBuf b; r <- fromBuf b
                        y <- fromBuf b
                        pure (IDelayed fc r y)
               19 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IDelay fc y)
               20 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IForce fc y)

               21 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuote fc y)
               22 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuoteName fc y)
               23 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IQuoteDecl fc y)
               24 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IUnquote fc y)
               25 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IRunElab fc y)

               26 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IPrimVal fc y)
               27 => do fc <- fromBuf b
                        pure (IType fc)
               28 => do fc <- fromBuf b; y <- fromBuf b
                        pure (IHole fc y)
               29 => do fc <- fromBuf b
                        i <- fromBuf b
                        pure (Implicit fc i)
               30 => do fc <- fromBuf b
                        ns <- fromBuf b
                        rhs <- fromBuf b
                        pure (IWithUnambigNames fc ns rhs)
               31 => do fc <- fromBuf b; fn <- fromBuf b
                        arg <- fromBuf b
                        pure (IAutoApp fc fn arg)
               _ => corrupt "RawImp"

  export
  TTC IFieldUpdate where
    toBuf b (ISetField p val)
        = do tag 0; toBuf b p; toBuf b val
    toBuf b (ISetFieldApp p val)
        = do tag 1; toBuf b p; toBuf b val

    fromBuf b
        = case !getTag of
               0 => do p <- fromBuf b; val <- fromBuf b
                       pure (ISetField p val)
               1 => do p <- fromBuf b; val <- fromBuf b
                       pure (ISetFieldApp p val)
               _ => corrupt "IFieldUpdate"

  export
  TTC BindMode where
    toBuf b (PI r) = do tag 0; toBuf b r
    toBuf b PATTERN = tag 1
    toBuf b NONE = tag 2
    toBuf b COVERAGE = tag 3

    fromBuf b
        = case !getTag of
               0 => do x <- fromBuf b
                       pure (PI x)
               1 => pure PATTERN
               2 => pure NONE
               3 => pure COVERAGE
               _ => corrupt "BindMode"

  export
  TTC AltType where
    toBuf b FirstSuccess = tag 0
    toBuf b Unique = tag 1
    toBuf b (UniqueDefault x) = do tag 2; toBuf b x

    fromBuf b
        = case !getTag of
               0 => pure FirstSuccess
               1 => pure Unique
               2 => do x <- fromBuf b
                       pure (UniqueDefault x)
               _ => corrupt "AltType"

  export
  TTC ImpTy where
    toBuf b (MkImpTy fc nameFC n ty)
        = do toBuf b fc; toBuf b nameFC; toBuf b n; toBuf b ty
    fromBuf b
        = do fc <- fromBuf b; nameFC <- fromBuf b; n <- fromBuf b; ty <- fromBuf b
             pure (MkImpTy fc nameFC n ty)

  export
  TTC ImpClause where
    toBuf b (PatClause fc lhs rhs)
        = do tag 0; toBuf b fc; toBuf b lhs; toBuf b rhs
    toBuf b (ImpossibleClause fc lhs)
        = do tag 1; toBuf b fc; toBuf b lhs
    toBuf b (WithClause fc lhs wval prf flags cs)
        = do tag 2
             toBuf b fc
             toBuf b lhs
             toBuf b wval
             toBuf b prf
             toBuf b cs

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; lhs <- fromBuf b;
                       rhs <- fromBuf b
                       pure (PatClause fc lhs rhs)
               1 => do fc <- fromBuf b; lhs <- fromBuf b;
                       pure (ImpossibleClause fc lhs)
               2 => do fc <- fromBuf b; lhs <- fromBuf b;
                       wval <- fromBuf b; prf <- fromBuf b;
                       cs <- fromBuf b
                       pure (WithClause fc lhs wval prf [] cs)
               _ => corrupt "ImpClause"

  export
  TTC DataOpt where
    toBuf b (SearchBy ns)
        = do tag 0; toBuf b ns
    toBuf b NoHints = tag 1
    toBuf b UniqueSearch = tag 2
    toBuf b External = tag 3
    toBuf b NoNewtype = tag 4

    fromBuf b
        = case !getTag of
               0 => do ns <- fromBuf b
                       pure (SearchBy ns)
               1 => pure NoHints
               2 => pure UniqueSearch
               3 => pure External
               4 => pure NoNewtype
               _ => corrupt "DataOpt"

  export
  TTC ImpData where
    toBuf b (MkImpData fc n tycon opts cons)
        = do tag 0; toBuf b fc; toBuf b n; toBuf b tycon; toBuf b opts
             toBuf b cons
    toBuf b (MkImpLater fc n tycon)
        = do tag 1; toBuf b fc; toBuf b n; toBuf b tycon

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; n <- fromBuf b;
                       tycon <- fromBuf b; opts <- fromBuf b
                       cons <- fromBuf b
                       pure (MkImpData fc n tycon opts cons)
               1 => do fc <- fromBuf b; n <- fromBuf b;
                       tycon <- fromBuf b
                       pure (MkImpLater fc n tycon)
               _ => corrupt "ImpData"

  export
  TTC IField where
    toBuf b (MkIField fc c p n ty)
        = do toBuf b fc; toBuf b c; toBuf b p; toBuf b n; toBuf b ty

    fromBuf b
        = do fc <- fromBuf b; c <- fromBuf b; p <- fromBuf b
             n <- fromBuf b; ty <- fromBuf b
             pure (MkIField fc c p n ty)

  export
  TTC ImpRecord where
    toBuf b (MkImpRecord fc n ps con fs)
        = do toBuf b fc; toBuf b n; toBuf b ps; toBuf b con; toBuf b fs

    fromBuf b
        = do fc <- fromBuf b; n <- fromBuf b; ps <- fromBuf b
             con <- fromBuf b; fs <- fromBuf b
             pure (MkImpRecord fc n ps con fs)

  export
  TTC NoMangleDirective where
    toBuf b (CommonName n)
        = do tag 0; toBuf b n
    toBuf b (BackendNames ns)
        = do tag 1; toBuf b ns

    fromBuf b
        = case !getTag of
               0 => do n <- fromBuf b; pure (CommonName n)
               1 => do ns <- fromBuf b; pure (BackendNames ns)
               _ => corrupt "NoMangleDirective"

  export
  TTC FnOpt where
    toBuf b Inline = tag 0
    toBuf b NoInline = tag 12
    toBuf b TCInline = tag 11
    toBuf b Deprecate = tag 14
    toBuf b (Hint t) = do tag 1; toBuf b t
    toBuf b (GlobalHint t) = do tag 2; toBuf b t
    toBuf b ExternFn = tag 3
    toBuf b (ForeignFn cs) = do tag 4; toBuf b cs
    toBuf b Invertible = tag 5
    toBuf b (Totality Total) = tag 6
    toBuf b (Totality CoveringOnly) = tag 7
    toBuf b (Totality PartialOK) = tag 8
    toBuf b Macro = tag 9
    toBuf b (SpecArgs ns) = do tag 10; toBuf b ns
    toBuf b (NoMangle name) = do tag 13; toBuf b name

    fromBuf b
        = case !getTag of
               0 => pure Inline
               1 => do t <- fromBuf b; pure (Hint t)
               2 => do t <- fromBuf b; pure (GlobalHint t)
               3 => pure ExternFn
               4 => do cs <- fromBuf b; pure (ForeignFn cs)
               5 => pure Invertible
               6 => pure (Totality Total)
               7 => pure (Totality CoveringOnly)
               8 => pure (Totality PartialOK)
               9 => pure Macro
               10 => do ns <- fromBuf b; pure (SpecArgs ns)
               11 => pure TCInline
               12 => pure NoInline
               13 => do name <- fromBuf b; pure (NoMangle name)
               14 => pure Deprecate
               _ => corrupt "FnOpt"

  export
  TTC ImpDecl where
    toBuf b (IClaim fc c vis xs d)
        = do tag 0; toBuf b fc; toBuf b c; toBuf b vis; toBuf b xs; toBuf b d
    toBuf b (IData fc vis mbtot d)
        = do tag 1; toBuf b fc; toBuf b vis; toBuf b mbtot; toBuf b d
    toBuf b (IDef fc n xs)
        = do tag 2; toBuf b fc; toBuf b n; toBuf b xs
    toBuf b (IParameters fc vis d)
        = do tag 3; toBuf b fc; toBuf b vis; toBuf b d
    toBuf b (IRecord fc ns vis mbtot r)
        = do tag 4; toBuf b fc; toBuf b ns; toBuf b vis; toBuf b mbtot; toBuf b r
    toBuf b (INamespace fc xs ds)
        = do tag 5; toBuf b fc; toBuf b xs; toBuf b ds
    toBuf b (ITransform fc n lhs rhs)
        = do tag 6; toBuf b fc; toBuf b n; toBuf b lhs; toBuf b rhs
    toBuf b (IRunElabDecl fc tm)
        = do tag 7; toBuf b fc; toBuf b tm
    toBuf b (IPragma _ f) = throw (InternalError "Can't write Pragma")
    toBuf b (ILog n)
        = do tag 8; toBuf b n
    toBuf b (IBuiltin fc type name)
        = do tag 9; toBuf b fc; toBuf b type; toBuf b name

    fromBuf b
        = case !getTag of
               0 => do fc <- fromBuf b; c <- fromBuf b
                       vis <- fromBuf b;
                       xs <- fromBuf b; d <- fromBuf b
                       pure (IClaim fc c vis xs d)
               1 => do fc <- fromBuf b; vis <- fromBuf b
                       mbtot <- fromBuf b; d <- fromBuf b
                       pure (IData fc vis mbtot d)
               2 => do fc <- fromBuf b; n <- fromBuf b
                       xs <- fromBuf b
                       pure (IDef fc n xs)
               3 => do fc <- fromBuf b; vis <- fromBuf b
                       d <- fromBuf b
                       pure (IParameters fc vis d)
               4 => do fc <- fromBuf b; ns <- fromBuf b;
                       vis <- fromBuf b; mbtot <- fromBuf b;
                       r <- fromBuf b
                       pure (IRecord fc ns vis mbtot r)
               5 => do fc <- fromBuf b; xs <- fromBuf b
                       ds <- fromBuf b
                       pure (INamespace fc xs ds)
               6 => do fc <- fromBuf b; n <- fromBuf b
                       lhs <- fromBuf b; rhs <- fromBuf b
                       pure (ITransform fc n lhs rhs)
               7 => do fc <- fromBuf b; tm <- fromBuf b
                       pure (IRunElabDecl fc tm)
               8 => do n <- fromBuf b
                       pure (ILog n)
               9 => do fc <- fromBuf b
                       type <- fromBuf b
                       name <- fromBuf b
                       pure (IBuiltin fc type name)
               _ => corrupt "ImpDecl"


-- Log message with a RawImp
export
logRaw : {auto c : Ref Ctxt Defs} ->
         (s : String) ->
         {auto 0 _ : KnownTopic s} ->
         Nat -> Lazy String -> RawImp -> Core ()
logRaw str n msg tm
    = when !(logging str n) $
        do logString str n (msg ++ ": " ++ show tm)
