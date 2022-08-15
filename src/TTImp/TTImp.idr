module TTImp.TTImp

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Options
import Core.Options.Log
import Core.TT
import Core.Value

import Data.List
import Data.List1
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

%name BindMode bm

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
       IWithUnambigNames : FC -> List (FC, Name) -> RawImp' nm -> RawImp' nm

  %name RawImp' t, u

  public export
  IFieldUpdate : Type
  IFieldUpdate = IFieldUpdate' Name

  public export
  data IFieldUpdate' : Type -> Type where
       ISetField : (path : List String) -> RawImp' nm -> IFieldUpdate' nm
       ISetFieldApp : (path : List String) -> RawImp' nm -> IFieldUpdate' nm
  %name IFieldUpdate' upd

  public export
  AltType : Type
  AltType = AltType' Name

  public export
  data AltType' : Type -> Type where
       FirstSuccess : AltType' nm
       Unique : AltType' nm
       UniqueDefault : RawImp' nm -> AltType' nm
  %name AltType' alt

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
       -- Mark for export to a foreign language, list calling conventions
       ForeignExport : List (RawImp' nm) -> FnOpt' nm
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt' nm
       Totality : TotalReq -> FnOpt' nm
       Macro : FnOpt' nm
       SpecArgs : List Name -> FnOpt' nm
  %name FnOpt' fopt

  public export
  isTotalityReq : FnOpt' nm -> Bool
  isTotalityReq (Totality _) = True
  isTotalityReq _ = False

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
    show (ForeignExport cs) = "%export " ++ showSep " " (map show cs)
    show Invertible = "%invertible"
    show (Totality Total) = "total"
    show (Totality CoveringOnly) = "covering"
    show (Totality PartialOK) = "partial"
    show Macro = "%macro"
    show (SpecArgs ns) = "%spec " ++ showSep " " (map show ns)

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
    (ForeignExport xs) == (ForeignExport ys) = True -- xs == ys
    Invertible == Invertible = True
    (Totality tot_lhs) == (Totality tot_rhs) = tot_lhs == tot_rhs
    Macro == Macro = True
    (SpecArgs ns) == (SpecArgs ns') = ns == ns'
    _ == _ = False

  public export
  ImpTy : Type
  ImpTy = ImpTy' Name

  public export
  data ImpTy' : Type -> Type where
       MkImpTy : FC -> (nameFC : FC) -> (n : Name) -> (ty : RawImp' nm) -> ImpTy' nm

  %name ImpTy' ty

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
  %name DataOpt dopt

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

  %name ImpData' dat

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

  %name IField' fld

  public export
  ImpParameter : Type
  ImpParameter = ImpParameter' Name

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

  %name ImpRecord' rec

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
                    (rig : RigCount) -> (wval : RawImp' nm) -> -- with'd expression (& quantity)
                    (prf : Maybe Name) -> -- optional name for the proof
                    (flags : List WithFlag) ->
                    List (ImpClause' nm) -> ImpClause' nm
       ImpossibleClause : FC -> (lhs : RawImp' nm) -> ImpClause' nm

  %name ImpClause' cl

  export
  covering
  Show nm => Show (ImpClause' nm) where
    show (PatClause fc lhs rhs)
       = show lhs ++ " = " ++ show rhs
    show (WithClause fc lhs rig wval prf flags block)
       = show lhs
       ++ " with (" ++ show rig ++ " " ++ show wval ++ ")"
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
       IFail : FC -> Maybe String -> List (ImpDecl' nm) -> ImpDecl' nm
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

  %name ImpDecl' decl

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
    show (IFail _ msg decls)
        = "fail" ++ maybe "" ((" " ++) . show) msg ++ "\n" ++
          showSep "\n" (assert_total $ map (("  " ++) . show) decls)
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


export
mkWithClause : FC -> RawImp' nm -> List1 (RigCount, RawImp' nm, Maybe Name) ->
               List WithFlag -> List (ImpClause' nm) -> ImpClause' nm
mkWithClause fc lhs ((rig, wval, prf) ::: []) flags cls
  = WithClause fc lhs rig wval prf flags cls
mkWithClause fc lhs ((rig, wval, prf) ::: wp :: wps) flags cls
  = let vfc = virtualiseFC fc in
    WithClause fc lhs rig wval prf flags
      [mkWithClause fc (IApp vfc lhs (IBindVar vfc "arg")) (wp ::: wps) flags cls]

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

||| `definedInBlock` is used to figure out which definitions should
||| receive the additional arguments introduced by a Parameters directive
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
    defName ns (IFail _ _ nds) = concatMap (defName ns) nds
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
  getFC (IFail fc _ _) = fc
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
%name Arg' arg

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

-- Log message with a RawImp
export
logRaw : {auto c : Ref Ctxt Defs} ->
         (s : String) ->
         {auto 0 _ : KnownTopic s} ->
         Nat -> Lazy String -> RawImp -> Core ()
logRaw str n msg tm
    = when !(logging str n) $
        do logString str n (msg ++ ": " ++ show tm)
