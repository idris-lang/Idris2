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
import TTImp.ProcessData
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

import Data.List
import Data.Vect
import Data.Vect.Elem
import Data.Vect.Quantifiers
import Data.Maybe

import Libraries.Data.HVect

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
             NestedNames vars ->
             Visibility -> Name ->
             (params : List (Name, RigCount, PiInfo RawImp, RawImp)) ->
             (conName : Name) ->
             List IField ->
             Core ()
elabRecord {vars} eopts fc env nest vis tn params conName_in fields
    = do currentNS <- getNS -- Save the ns we are in.
         let Just conName' = parseConName conName_in
           | _ =>
               throw (GenericMsg fc $
                 "Invalid data constructor name: " ++ show conName_in)
         let conName = forgetUnqualifiedConName (toUnqualified conName')
         let Just tconName' = parseConName tn
           | _ => throw (GenericMsg fc $ "Invalid type constructor name: " ++ show tn)
         -- Namespace in which to define the type constructor.
         let ns = fromMaybe currentNS (toMbNamespace (get tconName'))
         let tconName' = toUnqualified tconName' ++ [ns]
         let tconNS = forgetQualifiedConName tconName'
         let mbInner = mbMkInnerNamespace (get tconName')
         -- Namespace in which to define the constructor and projections.
         let nsNested = maybe ns (\root => ns <.> mkNamespace root) mbInner
         elabAsData tconNS conName
         defs <- get Ctxt
         Just conty <- lookupTyExact (NS nsNested conName) (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ " failed"))

         -- Go into the nested namespace for elaboration of projections.
         setNS nsNested
         elabGetters tconNS conName nsNested 0 [] RF [] conty -- make postfix projections
         when !isPrefixRecordProjections $
           elabGetters tconNS conName nsNested 0 [] UN [] conty -- make prefix projections
         -- Restore to the previous namespace.
         setNS currentNS
  where
    paramTelescope : List (Maybe Name, RigCount, PiInfo RawImp, RawImp)
    paramTelescope = map jname params
      where
        jname : (Name, RigCount, PiInfo RawImp, RawImp)
             -> (Maybe Name, RigCount, PiInfo RawImp, RawImp)
        -- Record type parameters are implicit in the constructor
        -- and projections
        jname (n, _, _, t) = (Just n, erased, Implicit, t)

    fname : IField -> Name
    fname (MkIField fc c p n ty) = n

    farg : IField ->
           (Maybe Name, RigCount, PiInfo RawImp, RawImp)
    farg (MkIField fc c p n ty) = (Just n, c, p, ty)

    mkTy : List (Maybe Name, RigCount, PiInfo RawImp, RawImp) ->
           RawImp -> RawImp
    mkTy [] ret = ret
    mkTy ((n, c, imp, argty) :: args) ret
        = IPi EmptyFC c imp n argty (mkTy args ret)

    recTy : (tconNs : Name) -> RawImp
    recTy tconNs = apply (IVar fc tconNs) (map (\(n, c, p, tm) => (n, IVar EmptyFC n, p)) params)
      where
        ||| Apply argument to list of explicit or implicit named arguments
        apply : RawImp -> List (Name, RawImp, PiInfo RawImp) -> RawImp
        apply f [] = f
        apply f ((n, arg, Explicit) :: xs) = apply (IApp         (getFC f) f          arg) xs
        apply f ((n, arg, _       ) :: xs) = apply (INamedApp (getFC f) f n arg) xs

    elabAsData : Name -> Name -> Core ()
    elabAsData tconNs cname
        = do let conty = mkTy paramTelescope $
                         mkTy (map farg fields) (recTy tconNs)
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
                  Name ->
                  Namespace ->
                  (done : Nat) -> -- number of explicit fields processed
                  List (Name, RawImp) -> -- names to update in types
                    -- (for dependent records, where a field's type may depend
                    -- on an earlier projection)
                  (mkProjName : String -> Name) ->
                  Env Term vs -> Term vs ->
                  Core ()
    elabGetters tconNs con nsNested done upds mkProjName tyenv (Bind bfc n b@(Pi _ rc imp ty_chk) sc)
        = if (n `elem` map fst params) || (n `elem` vars)
             then elabGetters tconNs con nsNested
                              (if imp == Explicit && not (n `elem` vars)
                                  then S done else done)
                              upds mkProjName (b :: tyenv) sc
             else
                do let fldNameStr = nameRoot n
                   let projNameNS = NS nsNested (mkProjName fldNameStr)

                   ty <- unelab tyenv ty_chk
                   let ty' = substNames vars upds ty
                   log "declare.record.field" 5 $ "Field type: " ++ show ty'
                   let rname = MN "rec" 0

                   -- Claim the projection type
                   projTy <- bindTypeNames []
                                 (map fst params ++ map fname fields ++ vars) $
                                    mkTy paramTelescope $
                                      IPi fc top Explicit (Just rname) (recTy tconNs) ty'
                   log "declare.record.projection" 5 $ "Projection " ++ show projNameNS ++ " : " ++ show projTy
                   processDecl [] nest env
                       (IClaim fc (if isErased rc
                                      then erased
                                      else top) (projVis vis) [Inline] (MkImpTy EmptyFC EmptyFC projNameNS projTy))

                   -- Define the LHS and RHS
                   let lhs_exp
                          = apply (IVar fc con)
                                    (replicate done (Implicit fc True) ++
                                       (if imp == Explicit
                                           then [IBindVar EmptyFC fldNameStr]
                                           else []) ++
                                    (replicate (countExp sc) (Implicit fc True)))
                   let lhs = IApp fc (IVar fc projNameNS)
                                (if imp == Explicit
                                    then lhs_exp
                                    else INamedApp fc lhs_exp (UN fldNameStr)
                                             (IBindVar fc fldNameStr))
                   let rhs = IVar EmptyFC (UN fldNameStr)
                   log "declare.record.projection" 5 $ "Projection " ++ show lhs ++ " = " ++ show rhs
                   processDecl [] nest env
                       (IDef fc projNameNS [PatClause fc lhs rhs])

                   -- Move on to the next getter
                   let upds' = (n, IApp fc (IVar fc projNameNS) (IVar fc rname)) :: upds
                   elabGetters tconNs con nsNested
                               (if imp == Explicit
                                   then S done else done)
                               upds' mkProjName (b :: tyenv) sc

    elabGetters tconNs con nsNested done upds _ _ _ = pure ()

export
processRecord : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                List ElabOpt -> NestedNames vars ->
                Env Term vars ->
                Visibility -> ImpRecord -> Core ()
processRecord eopts nest env vis (MkImpRecord fc n ps cons fs)
    = elabRecord eopts fc env nest vis n ps cons fs
