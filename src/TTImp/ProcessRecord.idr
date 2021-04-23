module TTImp.ProcessRecord

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.UnifyState
import Core.Value

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp
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
             List ElabOpt -> FC -> Env Term vars ->
             NestedNames vars -> Maybe String ->
             Visibility -> Name ->
             (params : List (Name, RigCount, PiInfo RawImp, RawImp)) ->
             (conName : Name) ->
             List IField ->
             Core ()
elabRecord {vars} eopts fc env nest newns vis tn params conName_in fields
    = do conName <- inCurrentNS conName_in
         elabAsData conName
         defs <- get Ctxt
         Just conty <- lookupTyExact conName (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ "failed"))

         -- Go into new namespace, if there is one, for getters
         case newns of
              Nothing => elabGetters conName 0 [] [] conty
              Just ns =>
                   do let cns = currentNS defs
                      let nns = nestedNS defs
                      extendNS (mkNamespace ns)
                      newns <- getNS
                      elabGetters conName 0 [] [] conty
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
    farg (MkIField fc c p n ty) = (fc, Just n, c, p, ty)

    mkTy : List (FC, Maybe Name, RigCount, PiInfo RawImp, RawImp) ->
           RawImp -> RawImp
    mkTy [] ret = ret
    mkTy ((fc, n, c, imp, argty) :: args) ret
        = IPi fc c imp n argty (mkTy args ret)

    recTy : RawImp
    recTy = apply (IVar fc tn) (map (\(n, c, p, tm) => (n, IVar EmptyFC n, p)) params)
      where
        ||| Apply argument to list of explicit or implicit named arguments
        apply : RawImp -> List (Name, RawImp, PiInfo RawImp) -> RawImp
        apply f [] = f
        apply f ((n, arg, Explicit) :: xs) = apply (IApp         (getFC f) f          arg) xs
        apply f ((n, arg, _       ) :: xs) = apply (INamedApp (getFC f) f n arg) xs

    elabAsData : Name -> Core ()
    elabAsData cname
        = do let conty = mkTy paramTelescope $
                         mkTy (map farg fields) recTy
             let con = MkImpTy EmptyFC EmptyFC cname !(bindTypeNames [] (map fst params ++
                                           map fname fields ++ vars) conty)
             let dt = MkImpData fc tn !(bindTypeNames [] (map fst params ++
                                           map fname fields ++ vars)
                                         (mkDataTy fc params)) [] [con]
             log "declare.record" 5 $ "Record data type " ++ show dt
             processDecl [] nest env (IData fc vis dt)

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
                  Name ->
                  (done : Nat) -> -- number of explicit fields processed
                  List (Name, RawImp) -> -- names to update in types
                    -- (for dependent records, where a field's type may depend
                    -- on an earlier projection)
                  Env Term vs -> Term vs ->
                  Core ()
    elabGetters con done upds tyenv (Bind bfc n b@(Pi _ rc imp ty_chk) sc)
        = if (n `elem` map fst params) || (n `elem` vars)
             then elabGetters con
                              (if imp == Explicit && not (n `elem` vars)
                                  then S done else done)
                              upds (b :: tyenv) sc
             else
                do let fldNameStr = nameRoot n
                   rfNameNS <- inCurrentNS (RF fldNameStr)
                   unNameNS <- inCurrentNS (UN fldNameStr)

                   ty <- unelab tyenv ty_chk
                   let ty' = substNames vars upds ty
                   log "declare.record.field" 5 $ "Field type: " ++ show ty'
                   let rname = MN "rec" 0

                   -- Claim the projection type
                   projTy <- bindTypeNames []
                                 (map fst params ++ map fname fields ++ vars) $
                                    mkTy paramTelescope $
                                      IPi bfc top Explicit (Just rname) recTy ty'
                   log "declare.record.projection" 5 $ "Projection " ++ show rfNameNS ++ " : " ++ show projTy
                   processDecl [] nest env
                       (IClaim bfc (if isErased rc
                                      then erased
                                      else top) (projVis vis) [Inline] (MkImpTy EmptyFC EmptyFC rfNameNS projTy))

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
                                    else INamedApp bfc lhs_exp (UN fldNameStr)
                                             (IBindVar bfc fldNameStr))
                   let rhs = IVar EmptyFC (UN fldNameStr)
                   log "declare.record.projection" 5 $ "Projection " ++ show lhs ++ " = " ++ show rhs
                   processDecl [] nest env
                       (IDef bfc rfNameNS [PatClause bfc lhs rhs])

                   -- Make prefix projection aliases if requested
                   when !isPrefixRecordProjections $ do  -- beware: `!` is NOT boolean `not`!
                     -- Claim the type.
                     -- we just reuse `projTy` defined above
                     log "declare.record.projection.prefix" 5 $ "Prefix projection " ++ show unNameNS ++ " : " ++ show projTy
                     processDecl [] nest env
                         (IClaim bfc (if isErased rc
                                        then erased
                                        else top) (projVis vis) [Inline] (MkImpTy EmptyFC EmptyFC unNameNS projTy))

                     -- Define the LHS and RHS
                     let lhs = IVar bfc unNameNS
                     let rhs = IVar bfc rfNameNS
                     log "declare.record.projection.prefix" 5 $ "Prefix projection " ++ show lhs ++ " = " ++ show rhs
                     processDecl [] nest env
                         (IDef bfc unNameNS [PatClause bfc lhs rhs])

                   -- Move on to the next getter.
                   --
                   -- In upds, we use unNameNS (as opposed to rfNameNS or both)
                   -- because the field types will probably mention the UN versions of the projections.
                   let upds' = (n, IApp bfc (IVar bfc unNameNS) (IVar bfc rname)) :: upds
                   elabGetters con
                               (if imp == Explicit
                                   then S done else done)
                               upds' (b :: tyenv) sc

    elabGetters con done upds _ _ = pure ()

export
processRecord : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                List ElabOpt -> NestedNames vars ->
                Env Term vars -> Maybe String ->
                Visibility -> ImpRecord -> Core ()
processRecord eopts nest env newns vis (MkImpRecord fc n ps cons fs)
    = elabRecord eopts fc env nest newns vis n ps cons fs
