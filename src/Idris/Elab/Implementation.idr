module Idris.Elab.Implementation

import Core.Binary
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.TT
import Core.Unify

import Idris.Resugar
import Idris.Syntax

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.ProcessDecls
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

import Control.Monad.State
import Data.ANameMap
import Data.List
import Data.NameMap

%default covering

replaceSep : String -> String
replaceSep = pack . map toForward . unpack
  where
    toForward : Char -> Char
    toForward '\\' = '/'
    toForward x = x

mkImpl : FC -> Name -> List RawImp -> Name
mkImpl fc n ps
    = DN (show n ++ " implementation at " ++ replaceSep (show fc))
         (UN ("__Impl_" ++ show n ++ "_" ++
          showSep "_" (map show ps)))

bindConstraints : FC -> PiInfo RawImp ->
                  List (Maybe Name, RawImp) -> RawImp -> RawImp
bindConstraints fc p [] ty = ty
bindConstraints fc p ((n, ty) :: rest) sc
    = IPi fc top p n ty (bindConstraints fc p rest sc)

bindImpls : FC -> List (Name, RigCount, RawImp) -> RawImp -> RawImp
bindImpls fc [] ty = ty
bindImpls fc ((n, r, ty) :: rest) sc
    = IPi fc r Implicit (Just n) ty (bindImpls fc rest sc)

addDefaults : FC -> Name -> List Name -> List (Name, List ImpClause) ->
              List ImpDecl ->
              (List ImpDecl, List Name) -- Updated body, list of missing methods
addDefaults fc impName allms defs body
    = let missing = dropGot allms body in
          extendBody [] missing body
  where
    -- Given the list of missing names, if any are among the default definitions,
    -- add them to the body
    extendBody : List Name -> List Name -> List ImpDecl ->
                 (List ImpDecl, List Name)
    extendBody ms [] body = (body, ms)
    extendBody ms (n :: ns) body
        = case lookup n defs of
               Nothing => extendBody (n :: ms) ns body
               Just cs =>
                    -- If any method names appear in the clauses, they should
                    -- be applied to the constraint name __con because they
                    -- are going to be referring to the present implementation.
                    -- That is, default method implementations could depend on
                    -- other methods.
                    -- (See test idris2/interface014 for an example!)
                    let mupdates
                            = map (\n => (n, IImplicitApp fc (IVar fc n)
                                                          (Just (UN "__con"))
                                                          (IVar fc impName))) allms
                        cs' = map (substNamesClause [] mupdates) cs in
                        extendBody ms ns
                             (IDef fc n (map (substLocClause fc) cs') :: body)

    -- Find which names are missing from the body
    dropGot : List Name -> List ImpDecl -> List Name
    dropGot ms [] = ms
    dropGot ms (IDef _ n _ :: ds)
        = dropGot (filter (/= n) ms) ds
    dropGot ms (_ :: ds) = dropGot ms ds

getMethImps : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Env Term vars -> Term vars ->
              Core (List (Name, RigCount, RawImp))
getMethImps env (Bind fc x (Pi fc' c Implicit ty) sc)
    = do rty <- unelabNoSugar env ty
         ts <- getMethImps (Pi fc' c Implicit ty :: env) sc
         pure ((x, c, rty) :: ts)
getMethImps env tm = pure []

export
elabImplementation : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto m : Ref MD Metadata} ->
                     FC -> Visibility -> List FnOpt -> Pass ->
                     Env Term vars -> NestedNames vars ->
                     (implicits : List (Name, RigCount, RawImp)) ->
                     (constraints : List (Maybe Name, RawImp)) ->
                     Name ->
                     (ps : List RawImp) ->
                     (implName : Maybe Name) ->
                     (nusing : List Name) ->
                     Maybe (List ImpDecl) ->
                     Core ()
-- TODO: Refactor all these steps into separate functions
elabImplementation {vars} fc vis opts_in pass env nest is cons iname ps impln nusing mbody
    = do let impName_in = maybe (mkImpl fc iname ps) id impln
         impName <- inCurrentNS impName_in
         -- The interface name might be qualified, so check if it's an
         -- alias for something
         syn <- get Syn
         defs <- get Ctxt
         inames <- lookupCtxtName iname (gamma defs)
         let [cndata] = concatMap (\n => lookupName n (ifaces syn))
                                  (map fst inames)
             | [] => throw (UndefinedName fc iname)
             | ns => throw (AmbiguousName fc (map fst ns))
         let cn : Name = fst cndata
         let cdata : IFaceInfo = snd cndata

         Just ity <- lookupTyExact cn (gamma defs)
              | Nothing => throw (UndefinedName fc cn)
         Just conty <- lookupTyExact (iconstructor cdata) (gamma defs)
              | Nothing => throw (UndefinedName fc (iconstructor cdata))

         let impsp = nub (concatMap findIBinds ps ++
                          concatMap findIBinds (map snd cons))

         logTerm "elab.implementation" 3 ("Found interface " ++ show cn) ity
         log "elab.implementation" 3 $
                 " with params: " ++ show (params cdata)
                 ++ " and parents: " ++ show (parents cdata)
                 ++ " using implicits: " ++ show impsp
                 ++ " and methods: " ++ show (methods cdata) ++ "\n"
                 ++ "Constructor: " ++ show (iconstructor cdata) ++ "\n"
         logTerm "elab.implementation" 3 "Constructor type: " conty
         log "elab.implementation" 5 $ "Making implementation " ++ show impName

         -- 1. Build the type for the implementation
         -- Make the constraints auto implicit arguments, which can be explicitly
         -- given when using named implementations
         --    (cs : Constraints) -> Impl params
         -- Don't make it a hint if it's a named implementation
         let opts = maybe ([Inline, Hint True])
                          (const ([Inline])) impln

         let initTy = bindImpls fc is $ bindConstraints fc AutoImplicit cons
                         (apply (IVar fc iname) ps)
         let paramBinds = if !isUnboundImplicits
                          then findBindableNames True vars [] initTy
                          else []
         let impTy = doBind paramBinds initTy

         let impTyDecl = IClaim fc top vis opts (MkImpTy fc impName impTy)
         log "elab.implementation" 5 $ "Implementation type: " ++ show impTy

         when (typePass pass) $ processDecl [] nest env impTyDecl

         -- If the body is empty, we're done for now (just declaring that
         -- the implementation exists and define it later)
         when (defPass pass) $ maybe (pure ())
           (\body_in => do
               defs <- get Ctxt
               Just impTyc <- lookupTyExact impName (gamma defs)
                    | Nothing => throw (InternalError ("Can't happen, can't find type of " ++ show impName))
               methImps <- getMethImps [] impTyc
               log "elab.implementation" 3 $ "Bind implicits to each method: " ++ show methImps

               -- 1.5. Lookup default definitions and add them to to body
               let (body, missing)
                     = addDefaults fc impName (map (dropNS . fst) (methods cdata))
                                      (defaults cdata) body_in

               log "elab.implementation" 5 $ "Added defaults: body is " ++ show body
               log "elab.implementation" 5 $ "Missing methods: " ++ show missing

               -- Add the 'using' hints
               defs <- get Ctxt
               let hs = openHints defs -- snapshot open hint state
               log "elab.implementation" 10 $ "Open hints: " ++ (show (impName :: nusing))
               traverse_ (\n => do n' <- checkUnambig fc n
                                   addOpenHint n') nusing

               -- 2. Elaborate top level function types for this interface
               defs <- get Ctxt
               fns <- topMethTypes [] impName methImps impsp
                                      (implParams cdata) (params cdata)
                                      (map fst (methods cdata))
                                      (methods cdata)
               traverse_ (processDecl [] nest env) (map mkTopMethDecl fns)

               -- 3. Build the record for the implementation
               let mtops = map (Builtin.fst . snd) fns
               let con = iconstructor cdata
               let ilhs = impsApply (IVar fc impName)
                                    (map (\x => (x, IBindVar fc (show x)))
                                              (map fst methImps))
               -- RHS is the constructor applied to a search for the necessary
               -- parent constraints, then the method implementations
               defs <- get Ctxt
               let fldTys = getFieldArgs !(normaliseHoles defs [] conty)
               log "elab.implementation" 5 $ "Field types " ++ show fldTys
               let irhs = apply (IVar fc con)
                                (map (const (ISearch fc 500)) (parents cdata)
                                 ++ map (mkMethField methImps fldTys) fns)
               let impFn = IDef fc impName [PatClause fc ilhs irhs]
               log "elab.implementation" 5 $ "Implementation record: " ++ show impFn

               -- If it's a named implementation, add it as a global hint while
               -- elaborating the record and bodies
               maybe (pure ()) (\x => addOpenHint impName) impln

               -- Make sure we don't use this name to solve parent constraints
               -- when elaborating the record, or we'll end up in a cycle!
               setFlag fc impName BlockedHint
               traverse (processDecl [] nest env) [impFn]
               unsetFlag fc impName BlockedHint

               setFlag fc impName TCInline
               -- it's the methods we're interested in, not the implementation
               setFlag fc impName (SetTotal PartialOK)

               -- 4. (TODO: Order method bodies to be in declaration order, in
               --    case of dependencies)

               -- 5. Elaborate the method bodies
               let upds = map methNameUpdate fns
               body' <- traverse (updateBody upds) body
               log "elab.implementation" 10 $ "Implementation body: " ++ show body'
               traverse (processDecl [] nest env) body'

               -- 6. Add transformation rules for top level methods
               traverse (addTransform impName upds) (methods cdata)

               -- inline flag has done its job, and outside the interface
               -- it can hurt, so unset it now
               unsetFlag fc impName TCInline

               -- Reset the open hints (remove the named implementation)
               setOpenHints hs
               pure ()) mbody
  where
    -- For the method fields in the record, get the arguments we need to abstract
    -- over
    getFieldArgs : Term vs -> List (Name, List (Name, RigCount, PiInfo RawImp))
    getFieldArgs (Bind _ x (Pi _ _ _ ty) sc)
        = (x, getArgs ty) :: getFieldArgs sc
      where
        getArgs : Term vs' -> List (Name, RigCount, PiInfo RawImp)
        getArgs (Bind _ x (Pi _ c p _) sc)
            = (x, c, forgetDef p) :: getArgs sc
        getArgs _ = []
    getFieldArgs _ = []

    impsApply : RawImp -> List (Name, RawImp) -> RawImp
    impsApply fn [] = fn
    impsApply fn ((n, arg) :: ns)
        = impsApply (IImplicitApp fc fn (Just n) arg) ns

    mkLam : List (Name, RigCount, PiInfo RawImp) -> RawImp -> RawImp
    mkLam [] tm = tm
    mkLam ((x, c, p) :: xs) tm
        = ILam fc c p (Just x) (Implicit fc False) (mkLam xs tm)

    applyTo : FC -> RawImp -> List (Name, RigCount, PiInfo RawImp) -> RawImp
    applyTo fc tm [] = tm
    applyTo fc tm ((x, c, Explicit) :: xs)
        = applyTo fc (IApp fc tm (IVar fc x)) xs
    applyTo fc tm ((x, c, AutoImplicit) :: xs)
        = applyTo fc (IImplicitApp fc tm (Just x) (IVar fc x)) xs
    applyTo fc tm ((x, c, Implicit) :: xs)
        = applyTo fc (IImplicitApp fc tm (Just x) (IVar fc x)) xs
    applyTo fc tm ((x, c, DefImplicit _) :: xs)
        = applyTo fc (IImplicitApp fc tm (Just x) (IVar fc x)) xs

    -- When applying the method in the field for the record, eta expand
    -- the expected arguments based on the field type, so that implicits get
    -- inserted in the right place
    mkMethField : List (Name, RigCount, RawImp) ->
                  List (Name, List (Name, RigCount, PiInfo RawImp)) ->
                  (Name, Name, List (String, String), RigCount, Maybe TotalReq, RawImp) -> RawImp
    mkMethField methImps fldTys (topn, n, upds, c, treq, ty)
        = let argns = map applyUpdate (maybe [] id (lookup (dropNS topn) fldTys))
              imps = map fst methImps in
              -- Pass through implicit arguments to the function which are also
              -- implicit arguments to the declaration
              mkLam argns
                    (impsApply
                         (applyTo fc (IVar fc n) argns)
                         (map (\n => (n, IVar fc (UN (show n)))) imps))
      where
        applyUpdate : (Name, RigCount, PiInfo RawImp) ->
                      (Name, RigCount, PiInfo RawImp)
        applyUpdate (UN n, c, p)
            = maybe (UN n, c, p) (\n' => (UN n', c, p)) (lookup n upds)
        applyUpdate t = t

    methName : Name -> Name
    methName (NS _ n) = methName n
    methName n
        = DN (show n)
             (UN (show n ++ "_" ++ show iname ++ "_" ++
                     maybe "" show impln ++ "_" ++
                     showSep "_" (map show ps)))

    applyCon : Name -> Name -> Core (Name, RawImp)
    applyCon impl n
        = do mn <- inCurrentNS (methName n)
             pure (dropNS n, IVar fc mn)

    bindImps : List (Name, RigCount, RawImp) -> RawImp -> RawImp
    bindImps [] ty = ty
    bindImps ((n, c, t) :: ts) ty
        = IPi fc c Implicit (Just n) t (bindImps ts ty)

    -- Return method name, specialised method name, implicit name updates,
    -- and method type. Also return how the method name should be updated
    -- in later method types (specifically, putting implicits in)
    topMethType : List (Name, RawImp) ->
                  Name -> List (Name, RigCount, RawImp) ->
                  List String -> List Name -> List Name -> List Name ->
                  (Name, RigCount, Maybe TotalReq, (Bool, RawImp)) ->
                  Core ((Name, Name, List (String, String), RigCount, Maybe TotalReq, RawImp),
                           List (Name, RawImp))
    topMethType methupds impName methImps impsp imppnames pnames allmeths (mn, c, treq, (d, mty_in))
        = do -- Get the specialised type by applying the method to the
             -- parameters
             n <- inCurrentNS (methName mn)

             -- Avoid any name clashes between parameters and method types by
             -- renaming IBindVars in the method types which appear in the
             -- parameters
             let upds' = !(traverse (applyCon impName) allmeths)
             let mty_in = substNames vars upds' mty_in
             let (upds, mty_in) = runState [] (renameIBinds impsp (findImplicits mty_in) mty_in)
             -- Finally update the method type so that implicits from the
             -- parameters are passed through to any earlier methods which
             -- appear in the type
             let mty_in = substNames vars methupds mty_in

             -- Substitute _ in for the implicit parameters, then
             -- substitute in the explicit parameters.
             let mty_iparams
                   = substBindVars vars
                                (map (\n => (n, Implicit fc False)) imppnames)
                                mty_in
             let mty_params
                   = substNames vars (zip pnames ps) mty_iparams
             log "elab.implementation" 5 $ "Substitute implicits " ++ show imppnames ++
                     " parameters " ++ show (zip pnames ps) ++
                     " "  ++ show mty_in ++ " is " ++
                     show mty_params

             let mbase = bindImps methImps $
                         bindConstraints fc AutoImplicit cons $
                         mty_params
             let ibound = findImplicits mbase

             mty <- bindTypeNamesUsed ibound vars mbase

             log "elab.implementation" 3 $
                     "Method " ++ show mn ++ " ==> " ++
                     show n ++ " : " ++ show mty
             log "elab.implementation" 3 $ "    (initially " ++ show mty_in ++ ")"
             log "elab.implementation" 5 $ "Updates " ++ show methupds
             log "elab.implementation" 5 $ "From " ++ show mbase
             log "elab.implementation" 3 $ "Name updates " ++ show upds
             log "elab.implementation" 3 $ "Param names: " ++ show pnames
             log "elab.implementation" 10 $ "Used names " ++ show ibound
             let ibinds = map fst methImps
             let methupds' = if isNil ibinds then []
                             else [(n, impsApply (IVar fc n)
                                     (map (\x => (x, IBindVar fc (show x))) ibinds))]
             pure ((mn, n, upds, c, treq, mty), methupds')

    topMethTypes : List (Name, RawImp) ->
                   Name -> List (Name, RigCount, RawImp) ->
                   List String ->
                   List Name -> List Name -> List Name ->
                   List (Name, RigCount, Maybe TotalReq, (Bool, RawImp)) ->
                   Core (List (Name, Name, List (String, String), RigCount, Maybe TotalReq, RawImp))
    topMethTypes upds impName methImps impsp imppnames pnames allmeths [] = pure []
    topMethTypes upds impName methImps impsp imppnames pnames allmeths (m :: ms)
        = do (m', newupds) <- topMethType upds impName methImps impsp imppnames pnames allmeths m
             ms' <- topMethTypes (newupds ++ upds) impName methImps impsp imppnames pnames allmeths ms
             pure (m' :: ms')

    mkTopMethDecl : (Name, Name, List (String, String), RigCount, Maybe TotalReq, RawImp) -> ImpDecl
    mkTopMethDecl (mn, n, upds, c, treq, mty)
        = let opts = maybe opts_in (\t => Totality t :: opts_in) treq in
              IClaim fc c vis opts (MkImpTy fc n mty)

    -- Given the method type (result of topMethType) return the mapping from
    -- top level method name to current implementation's method name
    methNameUpdate : (Name, Name, t) -> (Name, Name)
    methNameUpdate (mn, fn, _) = (UN (nameRoot mn), fn)

    findMethName : List (Name, Name) -> FC -> Name -> Core Name
    findMethName ns fc n
        = case lookup n ns of
               Nothing => throw (GenericMsg fc
                                (show n ++ " is not a method of " ++
                                 show iname))
               Just n' => pure n'

    updateApp : List (Name, Name) -> RawImp -> Core RawImp
    updateApp ns (IVar fc n)
        = do n' <- findMethName ns fc n
             pure (IVar fc n')
    updateApp ns (IApp fc f arg)
        = do f' <- updateApp ns f
             pure (IApp fc f' arg)
    updateApp ns (IImplicitApp fc f x arg)
        = do f' <- updateApp ns f
             pure (IImplicitApp fc f' x arg)
    updateApp ns tm
        = throw (GenericMsg (getFC tm) "Invalid method definition")

    updateClause : List (Name, Name) -> ImpClause ->
                   Core ImpClause
    updateClause ns (PatClause fc lhs rhs)
        = do lhs' <- updateApp ns lhs
             pure (PatClause fc lhs' rhs)
    updateClause ns (WithClause fc lhs wval flags cs)
        = do lhs' <- updateApp ns lhs
             cs' <- traverse (updateClause ns) cs
             pure (WithClause fc lhs' wval flags cs')
    updateClause ns (ImpossibleClause fc lhs)
        = do lhs' <- updateApp ns lhs
             pure (ImpossibleClause fc lhs')

    updateBody : List (Name, Name) -> ImpDecl -> Core ImpDecl
    updateBody ns (IDef fc n cs)
        = do cs' <- traverse (updateClause ns) cs
             n' <- findMethName ns fc n
             pure (IDef fc n' cs')
    updateBody ns _
        = throw (GenericMsg fc
                   "Implementation body can only contain definitions")

    addTransform : Name -> List (Name, Name) ->
                   (Name, RigCount, Maybe TotalReq, Bool, RawImp) ->
                   Core ()
    addTransform iname ns (top, _, _, _, ty)
        = do log "elab.implementation" 3 $
                     "Adding transform for " ++ show top ++ " : " ++ show ty ++
                     "\n\tfor " ++ show iname ++ " in " ++ show ns
             let lhs = IImplicitApp fc (IVar fc top)
                                       (Just (UN "__con"))
                                       (IVar fc iname)
             let Just mname = lookup (dropNS top) ns
                 | Nothing => pure ()
             let rhs = IVar fc mname
             log "elab.implementation" 5 $ show lhs ++ " ==> " ++ show rhs
             handleUnify
                 (processDecl [] nest env
                     (ITransform fc (UN (show top ++ " " ++ show iname)) lhs rhs))
                 (\err =>
                     log "elab.implementation" 5 $ "Can't add transform " ++
                                show lhs ++ " ==> " ++ show rhs ++
                             "\n\t" ++ show err)
