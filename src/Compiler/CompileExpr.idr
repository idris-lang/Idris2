module Compiler.CompileExpr

import Compiler.Opts.Constructor
import public Core.CompileExpr
import Core.Context.Log
import Core.Env
import Core.Options

import Core.Evaluate.Value
import Core.Evaluate.Expand
import Core.Evaluate.Quote
import Core.Evaluate.Normalise

import Data.SnocList
import Data.SnocList.Quantifiers
import Data.Vect

import Libraries.Data.NatSet
import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.Extra

%default covering

data Args
    = NewTypeBy Nat Nat
    | EraseArgs Nat NatSet
    | Arity Nat

||| Extract the number of arguments from a term, or return that it's
||| a newtype by a given argument position
numArgs : Defs -> Term vars -> Core Args
numArgs defs (Ref _ (TyCon arity) n) = pure (Arity arity)
numArgs defs (Ref _ _ n)
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure (Arity 0)
         case definition gdef of
           DCon di _ arity =>
               case newTypeArg di of
                    Nothing => pure (EraseArgs arity (eraseArgs gdef))
                    Just (_, pos) => pure (NewTypeBy arity pos)
           Function _ def _ _ => pure (EraseArgs (countArgs def) (eraseArgs gdef))
           ExternDef arity => pure (Arity arity)
           ForeignDef arity _ => pure (Arity arity)
           _ => pure (Arity 0)
  where
    countArgs : forall vars . Term vars -> Nat
    countArgs (Bind _ _ (Lam {}) sc) = S (countArgs sc)
    countArgs _ = 0
numArgs _ tm = pure (Arity 0)

weakenVar : Var ns -> Var (ns :< a)
weakenVar (MkVar p) = (MkVar (Later p))

etaExpand : Int -> Nat -> CExp vars -> List (Var vars) -> CExp vars
etaExpand i Z exp args = mkApp exp (map (mkLocal (getFC exp)) (reverse args))
  where
    mkLocal : FC -> (Var vars) -> CExp vars
    mkLocal fc (MkVar p) = CLocal fc p

    mkApp : CExp vars -> List (CExp vars) -> CExp vars
    mkApp tm [] = tm
    mkApp (CApp fc f args) args' = CApp fc f (args ++ args')
    mkApp (CCon fc n ci t args) args' = CCon fc n ci t (args ++ args')
    mkApp (CExtPrim fc p args) args' = CExtPrim fc p (args ++ args')
    mkApp tm args = CApp (getFC tm) tm args
etaExpand i (S k) exp args
    = CLam (getFC exp) (MN "eta" i)
             (etaExpand (i + 1) k (weaken exp)
                  (first :: map later args))

export
expandToArity : Nat -> CExp vars -> List (CExp vars) -> CExp vars
-- No point in applying to anything
expandToArity _ (CErased fc) _ = CErased fc
-- Overapplied; apply everything as single arguments
expandToArity Z f args = applyAll f args
  where
    applyAll : CExp vars -> List (CExp vars) -> CExp vars
    applyAll fn [] = fn
    applyAll fn (a :: args) = applyAll (CApp (getFC fn) fn [a]) args
expandToArity (S k) f (a :: args) = expandToArity k (addArg f a) args
  where
    addArg : CExp vars -> CExp vars -> CExp vars
    addArg (CApp fc fn args) a = CApp fc fn (args ++ [a])
    addArg (CCon fc n ci tag args) a = CCon fc n ci tag (args ++ [a])
    addArg (CExtPrim fc p args) a = CExtPrim fc p (args ++ [a])
    addArg f a = CApp (getFC f) f [a]
-- Underapplied, saturate with lambdas
expandToArity num fn [] = etaExpand 0 num fn []

applyNewType : Nat -> Nat -> CExp vars -> List (CExp vars) -> CExp vars
applyNewType arity pos fn args
    = let fn' = expandToArity arity fn args in
          keepArg fn' -- fn' might be lambdas, after eta expansion
  where
    keep : Nat -> List (CExp vs) -> CExp vs
    keep i [] = CErased (getFC fn) -- can't happen if all is well!
    keep i (x :: xs)
        = if i == pos
             then x
             else keep (1 + i) xs

    keepArg : CExp vs -> CExp vs
    keepArg (CLam fc x sc) = CLam fc x (keepArg sc)
    keepArg (CCon fc _ _ _ args) = keep 0 args
    keepArg tm = CErased (getFC fn)

dropPos : NatSet -> CExp vs -> CExp vs
dropPos epos (CLam fc x sc) = CLam fc x (dropPos epos sc)
dropPos epos (CApp fc tm@(CApp {}) args')
    = CApp fc (dropPos epos tm) args'
dropPos epos (CApp fc f args) = CApp fc f (drop epos args)
dropPos epos (CCon fc c ci a args) = CCon fc c ci a (drop epos args)
dropPos epos tm = tm

eraseConArgs : Nat -> NatSet -> CExp vars -> List (CExp vars) -> CExp vars
eraseConArgs arity epos fn args
    = let fn' = expandToArity arity fn args in
          if isEmpty epos
             then fn'
             else dropPos epos fn' -- fn' might be lambdas, after eta expansion

mkDropSubst : NatSet ->
              (vars : Scope) ->
              (args : Scope) ->
              (SizeOf args) ->
              (args' ** Thin (Scope.addInner vars args') (Scope.addInner vars args))
mkDropSubst es rest l s with (sizedView s)
    mkDropSubst _ _ _ _ | Z = ([<] ** Refl)
    mkDropSubst es rest (xs :< x) _ | (S s@(MkSizeOf i _))
        = let (vs ** sub) = mkDropSubst es rest xs s in
            if i `elem` es
                then (vs ** Drop sub)
                else (vs :< x ** Keep sub)

-- See if the constructor is a special constructor type, e.g a nil or cons
-- shaped thing.
dconFlag : {auto c : Ref Ctxt Defs} ->
           Name -> Core ConInfo
dconFlag n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Can't find " ++ show n))
         pure (ciFlags (definition def) (flags def))
  where
    ciFlags : Def -> List DefFlag -> ConInfo
    ciFlags def [] = case def of
      TCon {} => TYCON
      _ => DATACON
    ciFlags def (ConType ci :: xs) = ci
    ciFlags def (x :: xs) = ciFlags def xs

toCExp : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref NextMN Int} ->
         Name -> Term vars ->
         Core (CExp vars)

toCExpScope : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref NextMN Int} ->
              Name -> Nat -> NatSet ->
              CaseScope vars -> Core (CCaseScope vars)
toCExpScope n i es (RHS _ tm) = pure $ CRHS !(toCExp n tm)
toCExpScope n i es (Arg c x sc)
    = if i `elem` es
            then pure $ shrinkCScope (Drop Refl) $
                        !(toCExpScope n (S i) es sc)
            else pure $ CArg x !(toCExpScope n (S i) es sc)

conCases : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref NextMN Int} ->
           Name -> List (CaseAlt vars) ->
           Core (List (CConAlt vars))
conCases n [] = pure []
conCases n (ConCase fc x tag sc :: ns)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact x (gamma defs)
              | Nothing => -- primitive type match
                   do xn <- getFullName x
                      pure $ MkConAlt xn TYCON Nothing !(toCExpScope n 0 NatSet.empty sc)
                               :: !(conCases n ns)
         let nt = case definition gdef of
                       DCon di _ arity => newTypeArg di
                       _ => Nothing
         case nt of
              Just pos => conCases n ns -- skip it
              _ => do xn <- getFullName x
                      sc' <- toCExpScope n 0 (eraseArgs gdef) sc
                      ns' <- conCases n ns
                      if dcon (definition gdef)
                         then pure $ MkConAlt xn !(dconFlag xn) (Just tag) sc' :: ns'
                         else pure $ MkConAlt xn !(dconFlag xn) Nothing sc' :: ns'
  where
    dcon : Def -> Bool
    dcon (DCon _ _ _) = True
    dcon _ = False

conCases n (_ :: ns) = conCases n ns

constCases : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref NextMN Int} ->
             Name -> List (CaseAlt vars) ->
             Core (List (CConstAlt vars))
constCases n [] = pure []
constCases n (ConstCase _ WorldVal sc :: ns)
    = constCases n ns
constCases n (ConstCase _ x sc :: ns)
    = pure $ MkConstAlt x !(toCExp n sc) ::
                  !(constCases n ns)
constCases n (_ :: ns) = constCases n ns

getDef : {auto c : Ref Ctxt Defs} ->
         {auto s : Ref NextMN Int} ->
         Name -> List (CaseAlt vars) ->
         Core (Maybe (CExp vars))
getDef n [] = pure Nothing
getDef n (DefaultCase fc sc :: ns)
    = pure $ Just !(toCExp n sc)
getDef n (ConstCase fc WorldVal sc :: ns)
    = pure $ Just !(toCExp n sc)
getDef n (_ :: ns) = getDef n ns

-- If there's a case which matches on a 'newtype', return the RHS
-- without matching.
-- Take some care if the newtype involves a WorldVal - in that case we
-- still need to let bind the scrutinee to ensure it's evaluated exactly
-- once.
getNewType : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref NextMN Int} ->
             FC -> CExp vars ->
             Name -> List (CaseAlt vars) ->
             Core (Maybe (CExp vars))
getNewType fc scr n [] = pure Nothing
getNewType fc scr n (DefaultCase _ sc :: ns)
    = pure $ Nothing
getNewType fc scr n (ConCase _ x tag sc :: ns)
    = do defs <- get Ctxt
         Just (DCon di t a) <- lookupDefExact x (gamma defs)
              | _ => pure Nothing
         let Just (noworld, pos) = newTypeArg di
              | _ => pure Nothing
         if noworld
            then substScr 0 pos scr Lin sc
            else substLetScr 0 pos scr Lin sc
  where
    -- no %World, so substitute diretly
    substScr : {args : _} ->
               Nat -> Nat -> CExp vars ->
               SubstCEnv args vars ->
               CaseScope (vars ++ args) ->
               Core (Maybe (CExp vars))
    substScr i pos x env (RHS _ tm)
        = do tm' <- toCExp n tm
             pure $ Just (substs (mkSizeOf args) env tm')
    substScr i pos x env (Arg c n sc)
        = if i == pos
             then substScr (S i) pos x (env :< x) sc
             else substScr (S i) pos x (env :< CErased fc) sc

    -- When we find the scrutinee, let bind it and substitute the name into
    -- the RHS, so the thing still gets evaluated if it's an action on %World
    substLetScr : {args : _} ->
               Nat -> Nat -> CExp vars ->
               SubstCEnv args (vars :< MN "eff" 0) ->
               CaseScope (vars ++ args) ->
               Core (Maybe (CExp vars))
    substLetScr i pos x env (RHS _ tm)
        = do tm' <- toCExp n tm
             let tm' = insertNames {outer = vars} {inner = args} {middle = [<MN "eff" 0]}
                            (mkSizeOf _) (mkSizeOf _) tm'
             let rettm = CLet fc (MN "eff" 0) NotInline x
                       (substs (mkSizeOf args) env tm')
             pure $ Just rettm
    substLetScr i pos x env (Arg c n sc)
        = if i == pos
             then substLetScr (S i) pos x (env :< CLocal fc First) sc
             else substLetScr (S i) pos x (env :< CErased fc) sc

getNewType fc scr n (_ :: ns) = getNewType fc scr n ns

toCExpCase : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref NextMN Int} ->
             Name -> FC -> CExp vars -> List (CaseAlt vars) ->
             Core (CExp vars)
toCExpCase n fc x (DelayCase _ ty arg sc :: rest)
    = pure $
          CLet fc ty YesInline (CErased fc) $
          CLet fc arg YesInline (CForce fc LInf (weaken x)) $
               !(toCExp n sc)
toCExpCase n fc sc alts@(ConCase _ _ _ _ :: _)
    = do Nothing <- getNewType fc sc n alts
             | Just def => pure def
         defs <- get Ctxt
         cases <- conCases n alts
         def <- getDef n alts
         if isNil cases
            then pure (fromMaybe (CErased fc) def)
            else pure (CConCase fc sc cases def)
toCExpCase n fc sc alts@(ConstCase _ _ _ :: _)
    = do cases <- constCases n alts
         def <- getDef n alts
         if isNil cases
            then pure (fromMaybe (CErased fc) def)
            else pure $ CConstCase fc sc cases def
toCExpCase n fc _ alts@(DefaultCase _ tm :: _) = toCExp n tm
toCExpCase n fc sc []
      = pure $ CCrash fc $ "Missing case tree in " ++ show n

toCExpTm : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref NextMN Int} ->
           Name -> Term vars ->
           Core (CExp vars)
toCExpTm n (Local fc _ _ prf)
    = pure $ CLocal fc prf
toCExpTm n (Ref fc (DataCon tag arity) fn)
    = do -- get full name for readability, and %builtin Natural
         cn <- getFullName fn
         fl <- dconFlag cn
         pure $ CCon fc cn fl (Just tag) []
toCExpTm n (Ref fc (TyCon arity) fn)
    = pure $ CCon fc fn TYCON Nothing []
toCExpTm n (Ref fc _ fn)
    = do full <- getFullName fn
             -- ^ For readability of output code, and the Nat hack,
         pure $ CApp fc (CRef fc full) []
toCExpTm n (Meta fc mn i args)
    = pure $ CApp fc (CRef fc mn) !(traverse (toCExp n) (map snd args))
toCExpTm n (Bind fc x (Lam {}) sc)
    = pure $ CLam fc x !(toCExp n sc)
toCExpTm n (Bind fc x (Let _ rig val _) sc)
    = do sc' <- toCExp n sc
         pure $ branchZero (shrinkCExp (Drop Refl) sc')
                        (CLet fc x YesInline !(toCExp n val) sc')
                        rig
toCExpTm n (Bind fc x (Pi _ c e ty) sc)
    = pure $ CCon fc (UN (Basic "->")) TYCON Nothing
                     [ !(toCExp n ty)
                     , CLam fc x !(toCExp n sc)]
toCExpTm n (Bind fc x b tm) = pure $ CErased fc
-- We'd expect this to have been dealt with in toCExp, but for completeness...
toCExpTm n (App fc tm _ arg)
    = pure $ CApp fc !(toCExp n tm) [!(toCExp n arg)]
-- This shouldn't be in terms any more, but here for completeness
toCExpTm n (As _ _ _ p) = toCExpTm n p
-- TODO: Either make sure 'Delayed' is always Rig0, or add to typecase
toCExpTm n (Case fc _ _ sc _ alts)
    = toCExpCase n fc !(toCExp n sc) alts
toCExpTm n (TDelayed fc _ _) = pure $ CErased fc
toCExpTm n (TDelay fc lr _ arg)
    = pure (CDelay fc lr !(toCExp n arg))
toCExpTm n (TForce fc lr arg)
    = pure (CForce fc lr !(toCExp n arg))
toCExpTm n (PrimVal fc $ PrT c) = pure $ CCon fc (UN $ Basic $ show c) TYCON Nothing [] -- Primitive type constant
toCExpTm n (PrimVal fc c) = pure $ CPrimVal fc c -- Non-type constant
toCExpTm n (PrimOp {arity} fc fn args)
    = pure $ COp fc fn !(traverseVect (toCExp n) args)
toCExpTm n (Erased fc _) = pure $ CErased fc
toCExpTm n (Unmatched fc str) = pure $ CCrash fc str
toCExpTm n (TType fc _) = pure $ CCon fc (UN (Basic "Type")) TYCON Nothing []

toCExp n tm
    = case getFnArgs tm of
           (f, args) =>
              do args' <- traverse (toCExp n) args
                 defs <- get Ctxt
                 f' <- toCExpTm n f
                 case !(numArgs defs f) of
                      NewTypeBy arity pos =>
                        pure $ applyNewType arity pos f' args'
                      EraseArgs arity epos =>
                        pure $ eraseConArgs arity epos f' args'
                      Arity a =>
                        pure $ expandToArity a f' args'

-- Need this for ensuring that argument list matches up to operator arity for
-- builtins
ArgList : Nat -> Scope -> Type
ArgList = HasLength

mkArgList : Int -> (n : Nat) -> (ns ** ArgList n ns)
mkArgList i Z = (_ ** Z)
mkArgList i (S k)
    = let (ns ** rec) = mkArgList (i - 1) k in
          (ns :< (MN "arg" (i - 1)) ** S rec)

data NArgs : Type where
     User : Name -> List (Glued [<]) -> NArgs
     Struct : String -> List (String, Glued [<]) -> NArgs
     NUnit : NArgs
     NPtr : NArgs
     NGCPtr : NArgs
     NBuffer : NArgs
     NForeignObj : NArgs
     NIORes : Glued [<] -> NArgs

getPArgs : {auto c : Ref Ctxt Defs} ->
           Defs -> Glued [<] -> Core (String, Glued [<])
getPArgs defs cl
    = do VDCon fc _ _ _ args <- expand cl
             | nf => throw (GenericMsg (getLoc nf) "Badly formed struct type")
         case !(traverseSnocList value args) of
              (_ :< n :< tydesc) =>
                  do VPrimVal _ (Str n') <- expand n
                         | nf => throw (GenericMsg (getLoc nf) "Unknown field name")
                     pure (n', tydesc)
              _ => throw (GenericMsg fc "Badly formed struct type")

getFieldArgs : {auto c : Ref Ctxt Defs} ->
               Defs -> Glued [<] -> Core (List (String, Glued [<]))
getFieldArgs defs cl
    = do VDCon fc _ _ _ args <- expand cl
             | nf => throw (GenericMsg (getLoc nf) "Badly formed struct type")
         case !(traverseSnocList value args) of
              -- cons
              [< _, t, rest] =>
                  do rest' <- getFieldArgs defs rest
                     (n, ty) <- getPArgs defs t
                     pure ((n, ty) :: rest')
              -- nil
              _ => pure []

getNArgs : {auto c : Ref Ctxt Defs} ->
           Defs -> Name -> List (Glued [<]) -> Core NArgs
getNArgs defs (NS _ (UN $ Basic "IORes")) [arg] = pure $ NIORes arg
getNArgs defs (NS _ (UN $ Basic "Ptr")) [arg] = pure NPtr
getNArgs defs (NS _ (UN $ Basic "AnyPtr")) [] = pure NPtr
getNArgs defs (NS _ (UN $ Basic "GCPtr")) [arg] = pure NGCPtr
getNArgs defs (NS _ (UN $ Basic "GCAnyPtr")) [] = pure NGCPtr
getNArgs defs (NS _ (UN $ Basic "Buffer")) [] = pure NBuffer
getNArgs defs (NS _ (UN $ Basic "ForeignObj")) [] = pure NForeignObj
getNArgs defs (NS _ (UN $ Basic "Unit")) [] = pure NUnit
getNArgs defs (NS _ (UN $ Basic "Struct")) [n, args]
    = do VPrimVal _ (Str n') <- expand n
             | nf => throw (GenericMsg (getLoc nf) "Unknown name for struct")
         pure (Struct n' !(getFieldArgs defs args))
getNArgs defs n args = pure $ User n args

-- The order of the arguments have a big effect on case-tree size
nfToCFType : {auto c : Ref Ctxt Defs} ->
             FC -> ClosedNF -> (inStruct : Bool) -> Core CFType
nfToCFType _ (VPrimVal _ $ PrT IntType) _ = pure CFInt
nfToCFType _ (VPrimVal _ $ PrT IntegerType) _ = pure CFInteger
nfToCFType _ (VPrimVal _ $ PrT Bits8Type) _ = pure CFUnsigned8
nfToCFType _ (VPrimVal _ $ PrT Bits16Type) _ = pure CFUnsigned16
nfToCFType _ (VPrimVal _ $ PrT Bits32Type) _ = pure CFUnsigned32
nfToCFType _ (VPrimVal _ $ PrT Bits64Type) _ = pure CFUnsigned64
nfToCFType _ (VPrimVal _ $ PrT Int8Type) _ = pure CFInt8
nfToCFType _ (VPrimVal _ $ PrT Int16Type) _ = pure CFInt16
nfToCFType _ (VPrimVal _ $ PrT Int32Type) _ = pure CFInt32
nfToCFType _ (VPrimVal _ $ PrT Int64Type) _ = pure CFInt64
nfToCFType _ (VPrimVal _ $ PrT StringType) False = pure CFString
nfToCFType fc (VPrimVal _ $ PrT StringType) True
    = throw (GenericMsg fc "String not allowed in a foreign struct")
nfToCFType _ (VPrimVal _ $ PrT DoubleType) _ = pure CFDouble
nfToCFType _ (VPrimVal _ $ PrT CharType) _ = pure CFChar
nfToCFType _ (VPrimVal _ $ PrT WorldType) _ = pure CFWorld
nfToCFType _ (VBind fc _ (Pi _ _ _ ty) sc) False
    = do defs <- get Ctxt
         sty <- nfToCFType fc !(expand ty) False
         sc' <- expand !(sc (pure (VErased fc Placeholder)))
         tty <- nfToCFType fc sc' False
         pure (CFFun sty tty)
nfToCFType _ (VBind fc _ _ _) True
    = throw (GenericMsg fc "Function types not allowed in a foreign struct")
nfToCFType _ (VTCon fc n_in _ args) s
    = do defs <- get Ctxt
         n <- toFullNames n_in
         case !(getNArgs defs n $ cast !(traverseSnocList value args)) of
              User un uargs =>
                do nargs <- traverse expand uargs
                   cargs <- traverse (\ arg => nfToCFType fc arg s) nargs
                   pure (CFUser n cargs)
              Struct n fs =>
                do fs' <- traverse
                             (\ (n, ty) =>
                                    do tynf <- expand ty
                                       tycf <- nfToCFType fc tynf False
                                       pure (n, tycf)) fs
                   pure (CFStruct n fs')
              NUnit => pure CFUnit
              NPtr => pure CFPtr
              NGCPtr => pure CFGCPtr
              NBuffer => pure CFBuffer
              NForeignObj => pure CFForeignObj
              NIORes uarg =>
                do narg <- expand uarg
                   carg <- nfToCFType fc narg s
                   pure (CFIORes carg)
nfToCFType _ (VType {}) s
    = pure (CFUser (UN (Basic "Type")) [])
nfToCFType _ (VErased {}) s
    = pure (CFUser (UN (Basic "__")) [])
nfToCFType fc t s
    = do defs <- get Ctxt
         ty <- quote Env.empty t
         throw (GenericMsg (getLoc t)
                       ("Can't marshal type for foreign call " ++
                                      show !(toFullNames ty)))

getCFTypes : {auto c : Ref Ctxt Defs} ->
             List CFType -> ClosedNF ->
             Core (List CFType, CFType)
getCFTypes args (VBind fc _ (Pi _ _ _ ty) sc)
    = do defs <- get Ctxt
         aty <- nfToCFType fc !(expand ty) False
         sc' <- expand !(sc (pure (VErased fc Placeholder)))
         getCFTypes (aty :: args) sc'
getCFTypes args t
    = pure (reverse args, !(nfToCFType (getLoc t) t False))

lamRHSenv : Int -> FC -> (ns : Scope) -> (SizeOf ns, SubstCEnv ns Scope.empty)
lamRHSenv i fc [<] = (zero, Subst.empty {tm = CExp})
lamRHSenv i fc (ns :< n)
    = let (s, env) = lamRHSenv (i + 1) fc ns in
      (suc s, env :< CRef fc (MN "x" i))

mkBounds : (xs : _) -> Bounds xs
mkBounds [<] = None
mkBounds (xs :< x) = Add x x (mkBounds xs)

getNewArgs : {done : _} ->
             SubstCEnv done args -> Scope
getNewArgs [<] = [<]
getNewArgs (xs :< CRef _ n) = getNewArgs xs :< n
getNewArgs {done = xs :< x} (sub :< _) = getNewArgs sub :< x

-- If a name is declared in one module and defined in another,
-- we have to assume arity 0 for incremental compilation because
-- we have no idea how it's defined, and when we made calls to the
-- function, they had arity 0.
lamRHS : (ns : Scope) -> CExp ns -> ClosedCExp
lamRHS ns tm
    = let (s, env) = lamRHSenv 0 (getFC tm) ns
          tmExp = substs s env (rewrite appendLinLeftNeutral ns in tm)
          newArgs = getNewArgs env
          bounds = mkBounds newArgs
          expLocs = mkLocals bounds zero {inner = Scope.empty} tmExp in
          lamBind (getFC tm) _ expLocs
  where
    lamBind : FC -> (ns : Scope) -> CExp ns -> ClosedCExp
    lamBind fc [<] tm = tm
    lamBind fc (ns :< n) tm = lamBind fc ns (CLam fc n tm)

toArgExp : (Var ns) -> CExp ns
toArgExp (MkVar p) = CLocal emptyFC p

-- Move any lambdas in the body of the definition into the lhs list of vars.
-- Annoyingly, the indices will need fixing up because the order in the top
-- level definition goes left to right (i.e. first argument has lowest index,
-- not the highest, as you'd expect if they were all lambdas).
export
mergeLambdas : (args : SnocList Name) -> CExp args -> (args' ** CExp args')
mergeLambdas args (CLam fc x sc)
    = mergeLambdas (args :< x) sc
mergeLambdas args exp = (args ** exp)

toCDef : {auto c : Ref Ctxt Defs} ->
         Name -> ClosedTerm -> NatSet -> Def ->
         Core CDef
toCDef n ty _ None
    = pure $ MkError $ CCrash emptyFC ("Encountered undefined name " ++ show !(getFullName n))
toCDef n ty erased (Function fi _ tree _)
    = do log "compiler.newtype.world" 25 "toCDef Function ty: \{show ty}, n: \{show n}, erased: \{show erased}, tree: \{show tree}"
         s <- newRef NextMN 0
         t <- toCExp n tree
         let (args ** comptree) = mergeLambdas [<] t
         let (args' ** p) = fromNatSet erased args
         log "compiler.newtype.world" 25 "toCDef Function comptree \{show comptree}, p: \{show p}, is_ext: \{show $ (externalDecl fi)}"
         let lam = toLam (externalDecl fi) $
            if NatSet.isEmpty erased
                then MkFun args comptree
                else MkFun (cast args') (shrinkCExp p comptree)
         log "compiler.newtype.world" 25 "toCDef Function is_erased: \{show $ NatSet.isEmpty erased}, lam \{show lam}, args': \{show $ Prelude.toList args'}"
         pure lam
  where
    toLam : Bool -> CDef -> CDef
    toLam True (MkFun args rhs) = MkFun Scope.empty (lamRHS args rhs)
    toLam _ d = d
toCDef n ty _ (ExternDef arity)
    = let (ns ** args) = mkArgList 0 arity in
          -- Reverse the args since we build them in the wrong order (most
          -- recently bound lambda is last argument to primitive)
          pure $ MkFun _ (CExtPrim emptyFC !(getFullName n)
                             (reverse (map toArgExp (getVars args))))
    where
        getVars : ArgList k ns -> List (Var ns)
        getVars Z = []
        getVars (S rest) = first :: map later (getVars rest)

toCDef n ty _ (ForeignDef arity cs)
    = do defs <- get Ctxt
         (atys, retty) <- getCFTypes [] !(expand !(nf Env.empty ty))
         pure $ MkForeign cs atys retty
toCDef n _ _ (DCon pos tag arity)
    = do let nt = snd <$> (newTypeArg pos)
         defs <- get Ctxt
         args <- numArgs {vars = Scope.empty} defs (Ref EmptyFC (DataCon tag arity) n)
         let arity' = case args of
                 NewTypeBy ar _ => ar
                 EraseArgs ar erased => ar `minus` size erased
                 Arity ar => ar
         pure $ MkCon (Just tag) arity' nt
toCDef n _ _ (TCon arity _ _ _ _ _ _)
    = pure $ MkCon Nothing arity Nothing
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef n ty _ (Hole {})
    = pure $ MkError $ CCrash emptyFC ("Encountered unimplemented hole " ++
                                       show !(getFullName n))
toCDef n ty _ (Guess {})
    = pure $ MkError $ CCrash emptyFC ("Encountered constrained hole " ++
                                       show !(getFullName n))
toCDef n ty _ (BySearch {})
    = pure $ MkError $ CCrash emptyFC ("Encountered incomplete proof search " ++
                                       show !(getFullName n))
toCDef n ty _ def
    = pure $ MkError $ CCrash emptyFC ("Encountered uncompilable name " ++
                                       show (!(getFullName n), def))

export
compileExp : {auto c : Ref Ctxt Defs} ->
             ClosedTerm -> Core ClosedCExp
compileExp tm
    = do s <- newRef NextMN 0
         exp <- toCExp (UN $ Basic "main") tm
         constructorCExp exp

||| Given a name, look up an expression, and compile it to a CExp in the environment
export
compileDef : {auto c : Ref Ctxt Defs} -> Name -> Core ()
compileDef n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
         -- If we're incremental, and the name has no definition yet, it
         -- might end up defined in another module, so leave it, but warn
         if noDefYet (definition gdef) (incrementalCGs !getSession)
           -- This won't be accurate if we have names declared in one module
           -- and defined elsewhere. It's tricky to do the complete check that
           -- we do for whole program compilation, though, since that involves
           -- traversing everything from the main expression.
           -- For now, consider it an incentive not to have cycles :).
            then recordWarning (GenericWarn emptyFC ("Compiling hole " ++ show n))
            else do log "compiler.newtype.world" 25 "compileDef name \{show n}, type gdef: \{show $ type gdef}"
                    s <- newRef NextMN 0
                    ce <- logDepth $ toCDef n (type gdef) (eraseArgs gdef)
                           !(toFullNames (definition gdef))
                    ce <- constructorCDef ce
                    setCompiled n ce
  where
    noDefYet : Def -> List CG -> Bool
    noDefYet None (_ :: _) = True
    noDefYet _ _ = False
