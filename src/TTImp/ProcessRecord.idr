module TTImp.ProcessRecord

import Core.Env
import Core.Metadata
import Core.UnifyState

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.BindImplicits
import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.TTImp.Traversals
import TTImp.Unelab
import TTImp.Utils

import Libraries.Data.WithDefault

import Data.String

%default covering

-- Used to remove the holes so that we don't end up with "hole is already defined"
-- errors because they've been duplicated when forming the various types of the
-- record constructor, getters, etc.
killHole : RawImp -> RawImp
killHole (IHole fc str) = Implicit fc True
killHole t = t

-- Projections are only visible if the record is public export
projVis : Visibility -> Visibility
projVis Public = Public
projVis _ = Private

elabRecord : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             List ElabOpt -> FC -> Env Term vars ->
             NestedNames vars -> Maybe String ->
             WithDefault Visibility Private ->
             Maybe TotalReq ->
             (tyName : Name) ->
             (params : List ImpParameter) ->
             (opts : List DataOpt) ->
             (conName : Name) ->
             List IField ->
             Core ()
elabRecord {vars} eopts fc env nest newns def_vis mbtot tn_in params0 opts conName_in fields
    = do tn <- inCurrentNS tn_in
         conName <- inCurrentNS conName_in
         params <- preElabAsData tn
         log "declare.record.parameters" 100 $
           unlines ("New list of parameters:" :: map (("  " ++) . displayParam) params)
         elabAsData tn conName params
         defs <- get Ctxt
         Just conty <- lookupTyExact conName (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ "failed"))

         -- #1404
         whenJust mbtot $ \tot => do
           log "declare.record" 5 $ "setting totality flag for " ++ show tn
           setFlag fc tn (SetTotal tot)

         -- Go into new namespace, if there is one, for getters
         case newns of
              Nothing => elabGetters tn conName params 0 [] Env.empty conty
              Just ns =>
                   do let cns = currentNS defs
                      let nns = nestedNS defs
                      extendNS (mkNamespace ns)
                      newns <- getNS
                      elabGetters tn conName params 0 [] Env.empty conty
                      -- Record that the current namespace is allowed to look
                      -- at private names in the nested namespace
                      update Ctxt { currentNS := cns,
                                    nestedNS := newns :: nns }

  where

    displayParam : ImpParameter -> String
    displayParam binder
      = withPiInfo binder.val.info "\{showCount binder.rig}\{show binder.name.val} : \{show binder.val.boundType}"

    paramTelescope : List ImpParameter -> List (AddFC $ WithRig $ WithMName (PiBindData RawImp))
    paramTelescope params = map jname params
      where
        jname : ImpParameter
             -> (AddFC $ WithRig $ WithMName (PiBindData RawImp))
        -- Record type parameters are implicit in the constructor
        -- and projections
        jname binder = Mk [EmptyFC, erased, Just binder.name] $ {info := Implicit} binder.val

    fname : IField -> Name
    fname field = field.name.val

    farg : IField -> AddFC (WithRig $ WithMName (PiBindData RawImp))
    farg field = Mk [virtualiseFC field.fc, field.rig, Just field.name] field.val

    mkTy : List (AddFC $ WithRig $ WithMName (PiBindData RawImp)) -> RawImp -> RawImp
    mkTy [] ret = ret
    mkTy (bind :: args) ret
        = IPi bind.fc bind.rig bind.val.info (map val bind.mName) bind.val.boundType (mkTy args ret)

    recTy : (tn : Name) -> -- fully qualified name of the record type
            (params : List ImpParameter) -> -- list of all the parameters
            RawImp
    recTy tn params = apply (IVar (virtualiseFC fc) tn) (map (\binder => (binder.name.val, IVar EmptyFC binder.name.val, binder.val.info)) params)
      where
        ||| Apply argument to list of explicit or implicit named arguments
        apply : RawImp -> List (Name, RawImp, PiInfo RawImp) -> RawImp
        apply f [] = f
        apply f ((n, arg, Explicit) :: xs) = apply (IApp         (getFC f) f          arg) xs
        apply f ((n, arg, _       ) :: xs) = apply (INamedApp (getFC f) f n arg) xs

    paramNames : List ImpParameter -> List Name
    paramNames params = map (.name.val) params

    mkDataTy : FC -> List ImpParameter -> RawImp
    mkDataTy fc [] = IType fc
    mkDataTy fc (binder :: ps) = IPi fc binder.rig binder.val.info (Just binder.name.val) binder.val.boundType (mkDataTy fc ps)

    nestDrop : Core (List (Name, Nat))
    nestDrop
      = do let assoc = map (\ (n, (_, ns, _)) => (n, length ns)) (names nest)
           traverse (\ (n, ns) => pure (!(toFullNames n), ns)) assoc

    -- Parameters may need implicit names to be bound e.g.
    --   record HasLength (xs : List a) (n : Nat)
    -- needs to be turned into
    --   record HasLength {0 a : Type} (xs : List a) (n : Nat)
    -- otherwise `a` will be bound as a field rather than a parameter!
    -- We pre-elaborate the datatype, thus resolving all the missing bindings,
    -- and return the new list of parameters
    preElabAsData : (tn : Name) -> -- fully qualified name of the record type
                    Core (List ImpParameter) -- New telescope of parameters, including missing bindings
    preElabAsData tn
        = do let fc = virtualiseFC fc
             let dataTy = IBindHere fc (PI erased) !(bindTypeNames fc [] (toList vars) (mkDataTy fc params0))
             defs <- get Ctxt
             -- Create a forward declaration if none exists
             when (isNothing !(lookupTyExact tn (gamma defs))) $ do
               let dt = MkImpLater fc tn dataTy
               log "declare.record" 10 $ "Pre-declare record data type: \{show dt}"
               processDecl [] nest env (IData fc def_vis mbtot dt)
             defs <- get Ctxt
             Just ty <- lookupTyExact tn (gamma defs)
               | Nothing => throw (InternalError "Missing data type \{show tn}, despite having just declared it!")
             log "declare.record" 20 "Obtained type: \{show ty}"
             (_ ** (tyenv, ty)) <- dropLeadingPis vars ty Env.empty
             ty <- unelabNest (NoSugar True) !nestDrop tyenv ty
             log "declare.record.parameters" 30 "Unelaborated type: \{show ty}"
             params <- getParameters [<] ty
             addMissingNames ([<] <>< map (\x => x.name) params0 ) params []

      where

        -- We have elaborated the record type in a context (e.g. variables bound on
        -- a LHS, or inside a `parameters` block) and so we need to start by dropping
        -- these local variables from the fully elaborated record's type
        -- We'll use the `env` thus obtained to unelab the remaining scope
        dropLeadingPis : {vs : _} -> (vars : Scope) -> Term vs -> Env Term vs ->
                         Core (vars' : Scope ** (Env Term vars', Term vars'))
        dropLeadingPis [<] ty env
          = do unless (null vars) $
                 logC "declare.record.parameters" 60 $ pure $ unlines
                   [ "We elaborated \{show tn} in a non-empty local context."
                   , "  Dropped: \{show vars}"
                   , "  Remaining type: \{show !(toFullNames ty)}"
                   ]
               pure (_ ** (env, ty))
        dropLeadingPis (vars :< var) (Bind fc n b@(Pi {}) ty) env
          = dropLeadingPis vars ty (Env.bind env b)
        dropLeadingPis _ ty _ = throw (InternalError "Malformed record type \{show ty}")

        getParameters :
          SnocList (WithRig $ WithMName $ PiBindData RawImp) -> -- accumulator
          RawImp' KindedName -> -- quoted type (some names may have disappeared)
          Core (SnocList (WithRig $ WithMName $ PiBindData RawImp))
        getParameters acc (IPi fc rig pinfo mnm argTy retTy)
          = let clean = mapTTImp killHole . map fullName in
            getParameters (acc :< (Mk [rig, map NoFC mnm] (MkPiBindData (map clean pinfo) (clean argTy)))) retTy
        getParameters acc (IType _) = pure acc
        getParameters acc ty = throw (InternalError "Malformed record type \{show ty}")

        addMissingNames :
          SnocList (WithFC Name) ->
          SnocList (WithRig $ WithMName $ PiBindData RawImp) ->
          List ImpParameter -> -- accumulator
          Core (List ImpParameter)
        addMissingNames (nms :< nm) (tele :< rest) acc
          = addMissingNames nms tele (Mk [rest.rig, nm] rest.val :: acc)
        addMissingNames [<] tele acc
          = do tele <- flip Core.traverseSnocList tele $ \ rest =>
                         case rest.mName of
                           Nothing => throw (InternalError "Some names have disappeared?! \{show rest.val}")
                           Just nm => pure (Mk [rest.rig, nm] rest.val) -- (nm, rest)
               unless (null tele) $
                 log "declare.record.parameters" 50 $
                   unlines ( "Decided to bind the following extra parameters:"
                           :: map (("  " ++) . displayParam) (tele <>> []))
               pure (tele <>> acc)

        addMissingNames nms [<] acc
          = throw (InternalError "Some arguments have disappeared")


    elabAsData : (tn : Name) -> -- fully qualified name of the record type
                 (conName : Name) -> -- fully qualified name of the record type constructor
                 (params : List ImpParameter) -> -- telescope of parameters
                 Core ()
    elabAsData tn cname params
        = do let fc = virtualiseFC fc
             let conty = mkTy (paramTelescope params) $
                         mkTy (map farg fields) (recTy tn params)
             let boundNames = paramNames params ++ map fname fields ++ (toList vars)
             let con = Mk [virtualiseFC fc, NoFC cname]
                       !(bindTypeNames fc [] boundNames conty)
             let dt = MkImpData fc tn Nothing opts [con]
             log "declare.record" 5 $ "Record data type " ++ show dt
             processDecl [] nest env (IData fc def_vis mbtot dt)

    countExp : Term vs -> Nat
    countExp (Bind _ _ (Pi _ _ Explicit _) sc) = S (countExp sc)
    countExp (Bind _ _ (Pi {}) sc) = countExp sc
    countExp _ = 0

    -- Generate getters from the elaborated record constructor type
    --
    -- WARNING: if you alter the names of the getters,
    --          you probably will have to adjust TTImp.TTImp.definedInBlock.
    --
    elabGetters : {vs : _} ->
                  (tn : Name) -> -- fully qualified name of the record type
                  (conName : Name) -> -- fully qualified name of the record type constructor
                  (params : List ImpParameter) -> -- Telescope of parameters
                  (done : Nat) -> -- number of explicit fields processed
                  List (Name, RawImp) -> -- names to update in types
                    -- (for dependent records, where a field's type may depend
                    -- on an earlier projection)
                  Env Term vs -> Term vs ->
                  Core ()
    elabGetters tn con params done upds tyenv (Bind bfc n b@(Pi _ rc imp ty_chk) sc)
        = let rig = if isErased rc then erased else top
              isVis = projVis (collapseDefault def_vis)
              paramNames = map (\x => x.name.val) params
          in if (n `elem` paramNames) || (n `elem` vars)
             then elabGetters tn con params
                              (if imp == Explicit && not (n `elem` vars)
                                  then S done else done)
                              upds (Env.bind tyenv b) sc
             else
                do let fldNameStr = nameRoot n
                   let unName = UN $ Basic fldNameStr
                   rfNameNS <- inCurrentNS (UN $ Field fldNameStr)
                   unNameNS <- inCurrentNS unName

                   ty <- unelabNest (NoSugar False) !nestDrop tyenv ty_chk
                   let ty' = substNames (toList vars) upds $ map rawName ty
                   log "declare.record.field" 5 $ "Field type: " ++ show ty'
                   let rname = MN "rec" 0

                   -- Claim the projection type
                   projTy <- bindTypeNames fc []
                                 (paramNames ++ map fname fields ++ toList vars) $
                                      mkTy (paramTelescope params) $
                                      IPi bfc top Explicit (Just rname) (recTy tn params) ty'
                   let fc' = virtualiseFC fc
                   let mkProjClaim = \ nm =>
                          let ty = Mk [fc', MkFCVal fc' nm] projTy
                          in IClaim (MkFCVal bfc (MkIClaimData rig isVis [Inline] ty))

                   log "declare.record.projection.claim" 5 $
                      "Projection " ++ show rfNameNS ++ ": " ++ show projTy
                   processDecl [] nest env (mkProjClaim rfNameNS)

                   -- Define the LHS and RHS
                   let lhs_exp
                          = apply (IVar bfc con)
                                    (replicate done (Implicit bfc True) ++
                                       (if imp == Explicit
                                           then [IBindVar fc' unName]
                                           else []) ++
                                    (replicate (countExp sc) (Implicit bfc True)))
                   let lhs = IApp bfc (IVar bfc rfNameNS)
                                (if imp == Explicit
                                    then lhs_exp
                                    else INamedApp bfc lhs_exp unName
                                             (IBindVar bfc unName))
                   let rhs = IVar fc' unName

                   -- EtaExpand implicits on both sides:
                   -- First, obtain all the implicit names in the prefix of
                   -- See idris-lang/Idris2#3467
                   (lhs, rhs) <- etaExpandImplicits fc' ty' lhs rhs

                   log "declare.record.projection.clause" 5 $ "Projection " ++ show lhs ++ " = " ++ show rhs
                   processDecl [] nest env
                       (IDef bfc rfNameNS [PatClause bfc lhs rhs])

                   -- Make prefix projection aliases if requested
                   when !isPrefixRecordProjections $ do  -- beware: `!` is NOT boolean `not`!
                     -- Claim the type.
                     -- we just reuse `projTy` defined above
                     log "declare.record.projection.prefix" 5 $
                       "Prefix projection " ++ show unNameNS ++ " : " ++ show projTy
                     processDecl [] nest env (mkProjClaim unNameNS)

                     -- Define the LHS and RHS
                     let lhs = IVar bfc unNameNS
                     let rhs = IVar bfc rfNameNS
                     log "declare.record.projection.prefix" 5 $
                       "Prefix projection " ++ show lhs ++ " = " ++ show rhs
                     processDecl [] nest env
                         (IDef bfc unNameNS [PatClause bfc lhs rhs])

                   -- Move on to the next getter.
                   --
                   -- In upds, we use unNameNS (as opposed to rfNameNS or both)
                   -- because the field types will probably mention the UN versions of the projections;
                   -- but only when prefix record projections are enabled, otherwise
                   -- dependent records won't typecheck!
                   --
                   -- With the braching on this flag, this change of using `rfNamesNS` remains backward compatible
                   -- (though the only difference I'm aware is in the output of the `:doc` command)
                   prefix_flag <- isPrefixRecordProjections
                   let upds' = if prefix_flag
                         then (n, IApp bfc (IVar bfc unNameNS) (IVar bfc rname)) :: upds
                         else (n, IApp bfc (IVar bfc rfNameNS) (IVar bfc rname)) :: upds

                   elabGetters tn con params
                               (if imp == Explicit
                                   then S done else done)
                               upds' (Env.bind tyenv b) sc

    elabGetters tn con _ done upds _ _ = pure ()

export
processRecord : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto o : Ref ROpts REPLOpts} ->
                List ElabOpt -> NestedNames vars ->
                Env Term vars -> Maybe String ->
                WithDefault Visibility Private -> Maybe TotalReq ->
                ImpRecord -> Core ()
processRecord eopts nest env newns def_vis mbtot rec@(MkWithData _ $ MkImpRecord header body)
    = elabRecord eopts rec.fc env nest newns def_vis mbtot header.name.val header.val body.opts body.name.val body.val
