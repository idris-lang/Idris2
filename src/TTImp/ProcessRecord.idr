module TTImp.ProcessRecord

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.UnifyState

import Idris.Syntax

import TTImp.BindImplicits
import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Unelab
import TTImp.Utils

import Data.List

%default covering

mkDataTy : FC -> List (Name, RigCount, PiInfo RawImp, RawImp) -> RawImp
mkDataTy fc [] = IType fc
mkDataTy fc ((n, c, p, ty) :: ps)
    = IPi fc c p (Just n) ty (mkDataTy fc ps)

-- Projections are only visible if the record is public export
projVis : Visibility -> Visibility
projVis Public = Public
projVis _ = Private

elabRecord : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             List ElabOpt -> FC -> Env Term vars ->
             NestedNames vars -> Maybe String ->
             Visibility -> Maybe TotalReq -> Name ->
             (params : List (Name, RigCount, PiInfo RawImp, RawImp)) ->
             (conName : Name) ->
             List IField ->
             Core ()
elabRecord {vars} eopts fc env nest newns vis mbtot tn_in params conName_in fields
    = do tn <- inCurrentNS tn_in
         conName <- inCurrentNS conName_in
         elabAsData tn conName
         defs <- get Ctxt
         Just conty <- lookupTyExact conName (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ "failed"))

         -- #1404
         case mbtot of
           Nothing  => pure ()
           Just tot => do
             log "declare.record" 5 $ "setting totality flag for " ++ show tn
             setFlag fc tn (SetTotal tot)

         -- Go into new namespace, if there is one, for getters
         case newns of
              Nothing => elabGetters tn conName 0 [] [] conty
              Just ns =>
                   do let cns = currentNS defs
                      let nns = nestedNS defs
                      extendNS (mkNamespace ns)
                      newns <- getNS
                      elabGetters tn conName 0 [] [] conty
                      defs <- get Ctxt
                      -- Record that the current namespace is allowed to look
                      -- at private names in the nested namespace
                      put Ctxt (record { currentNS = cns,
                                         nestedNS = newns :: nns } defs)

  where
    paramTelescope : List (FC, Maybe Name, RigCount, PiInfo RawImp, RawImp)
    paramTelescope = map jname params
      where
        jname : (Name, RigCount, PiInfo RawImp, RawImp)
             -> (FC, Maybe Name, RigCount, PiInfo RawImp, RawImp)
        -- Record type parameters are implicit in the constructor
        -- and projections
        jname (n, _, _, t) = (EmptyFC, Just n, erased, Implicit, t)

    fname : IField -> Name
    fname (MkIField fc c p n ty) = n

    farg : IField ->
           (FC, Maybe Name, RigCount, PiInfo RawImp, RawImp)
    farg (MkIField fc c p n ty) = (virtualiseFC fc, Just n, c, p, ty)

    mkTy : List (FC, Maybe Name, RigCount, PiInfo RawImp, RawImp) ->
           RawImp -> RawImp
    mkTy [] ret = ret
    mkTy ((fc, n, c, imp, argty) :: args) ret
        = IPi fc c imp n argty (mkTy args ret)

    recTy : (tn : Name) -> -- fully qualified name of the record type
            RawImp
    recTy tn = apply (IVar (virtualiseFC fc) tn) (map (\(n, c, p, tm) => (n, IVar EmptyFC n, p)) params)
      where
        ||| Apply argument to list of explicit or implicit named arguments
        apply : RawImp -> List (Name, RawImp, PiInfo RawImp) -> RawImp
        apply f [] = f
        apply f ((n, arg, Explicit) :: xs) = apply (IApp         (getFC f) f          arg) xs
        apply f ((n, arg, _       ) :: xs) = apply (INamedApp (getFC f) f n arg) xs

    elabAsData : (tn : Name) -> -- fully qualified name of the record type
                 (conName : Name) -> -- fully qualified name of the record type constructor
                 Core ()
    elabAsData tn cname
        = do let fc = virtualiseFC fc
             let conty = mkTy paramTelescope $
                         mkTy (map farg fields) (recTy tn)
             let con = MkImpTy EmptyFC EmptyFC cname !(bindTypeNames fc [] (map fst params ++
                                           map fname fields ++ vars) conty)
             let dt = MkImpData fc tn !(bindTypeNames fc [] (map fst params ++
                                           map fname fields ++ vars)
                                         (mkDataTy fc params)) [] [con]
             log "declare.record" 5 $ "Record data type " ++ show dt
             processDecl [] nest env (IData fc vis mbtot dt)

    countExp : Term vs -> Nat
    countExp (Bind _ _ (Pi _ _ Explicit _) sc) = S (countExp sc)
    countExp (Bind _ _ (Pi _ _ _ _) sc) = countExp sc
    countExp _ = 0

    -- Generate getters from the elaborated record constructor type
    --
    -- WARNING: if you alter the names of the getters,
    --          you probably will have to adjust TTImp.TTImp.definedInBlock.
    --
    elabGetters : {vs : _} ->
                  (tn : Name) -> -- fully qualified name of the record type
                  (conName : Name) -> -- fully qualified name of the record type constructor
                  (done : Nat) -> -- number of explicit fields processed
                  List (Name, RawImp) -> -- names to update in types
                    -- (for dependent records, where a field's type may depend
                    -- on an earlier projection)
                  Env Term vs -> Term vs ->
                  Core ()
    elabGetters tn con done upds tyenv (Bind bfc n b@(Pi _ rc imp ty_chk) sc)
        = let rig = if isErased rc then erased else top
              isVis = projVis vis
          in if (n `elem` map fst params) || (n `elem` vars)
             then elabGetters tn con
                              (if imp == Explicit && not (n `elem` vars)
                                  then S done else done)
                              upds (b :: tyenv) sc
             else
                do let fldNameStr = nameRoot n
                   rfNameNS <- inCurrentNS (UN $ Field fldNameStr)
                   unNameNS <- inCurrentNS (UN $ Basic fldNameStr)

                   let nestDrop
                          = map (\ (n, (_, ns, _)) => (n, length ns))
                                (names nest)
                   nestDrop <- traverse (\ (n, ns) => pure (!(toFullNames n), ns)) nestDrop
                   ty <- unelabNest nestDrop tyenv ty_chk
                   let ty' = substNames vars upds $ map rawName ty
                   log "declare.record.field" 5 $ "Field type: " ++ show ty'
                   let rname = MN "rec" 0

                   -- Claim the projection type
                   projTy <- bindTypeNames fc []
                                 (map fst params ++ map fname fields ++ vars) $
                                    mkTy paramTelescope $
                                      IPi bfc top Explicit (Just rname) (recTy tn) ty'

                   let mkProjClaim = \ nm =>
                          let ty = MkImpTy EmptyFC EmptyFC nm projTy
                          in IClaim bfc rig isVis [Inline] ty

                   log "declare.record.projection" 5 $
                      "Projection " ++ show rfNameNS ++ " : " ++ show projTy
                   processDecl [] nest env (mkProjClaim rfNameNS)

                   -- Define the LHS and RHS
                   let lhs_exp
                          = apply (IVar bfc con)
                                    (replicate done (Implicit bfc True) ++
                                       (if imp == Explicit
                                           then [IBindVar EmptyFC fldNameStr]
                                           else []) ++
                                    (replicate (countExp sc) (Implicit bfc True)))
                   let lhs = IApp bfc (IVar bfc rfNameNS)
                                (if imp == Explicit
                                    then lhs_exp
                                    else INamedApp bfc lhs_exp (UN $ Basic fldNameStr)
                                             (IBindVar bfc fldNameStr))
                   let rhs = IVar EmptyFC (UN $ Basic fldNameStr)
                   log "declare.record.projection" 5 $ "Projection " ++ show lhs ++ " = " ++ show rhs
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

                   elabGetters tn con
                               (if imp == Explicit
                                   then S done else done)
                               upds' (b :: tyenv) sc

    elabGetters tn con done upds _ _ = pure ()

export
processRecord : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Syn SyntaxInfo} ->
                List ElabOpt -> NestedNames vars ->
                Env Term vars -> Maybe String ->
                Visibility -> Maybe TotalReq ->
                ImpRecord -> Core ()
processRecord eopts nest env newns vis mbtot (MkImpRecord fc n ps cons fs)
    = elabRecord eopts fc env nest newns vis mbtot n ps cons fs
