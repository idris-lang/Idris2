module Idris.Elab.Interface

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Name
import Core.Env
import Core.Metadata
import Core.TT
import Core.Unify

import Idris.Doc.String
import Idris.REPL.Opts
import Idris.Syntax

import TTImp.BindImplicits
import TTImp.ProcessDecls
import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Utils

import Libraries.Data.ANameMap
import Libraries.Data.List.Extra
import Data.List
import Data.SnocList
import Libraries.Data.WithDefault

%default covering

------------------------------------------------------------------------
-- Signature

record Signature where
  constructor MkSignature
  count    : RigCount
  flags    : List FnOpt
  name     : WithFC Name
  isData   : Bool
  type     : RawImp

-- Give implicit Pi bindings explicit names, if they don't have one already,
-- because we need them to be consistent everywhere we refer to them
namePis : Int -> RawImp -> RawImp
namePis i (IPi fc r AutoImplicit Nothing ty sc)
    = IPi fc r AutoImplicit (Just (MN "i_con" i)) ty (namePis (i + 1) sc)
namePis i (IPi fc r Implicit Nothing ty sc)
    = IPi fc r Implicit (Just (MN "i_imp" i)) ty (namePis (i + 1) sc)
namePis i (IPi fc r p n ty sc)
    = IPi fc r p n ty (namePis i sc)
namePis i (IBindHere fc m ty) = IBindHere fc m (namePis i ty)
namePis i ty = ty

getSig : ImpDecl -> Maybe Signature
getSig (IClaim (MkFCVal _ $ MkIClaimData c _ opts (MkImpTy fc n ty)))
    = Just $ MkSignature { count    = c
                         , flags    = opts
                         , name     = n
                         , isData   = False
                         , type     = namePis 0 ty
                         }
getSig (IData _ _ _ (MkImpLater fc n ty))
    = Just $ MkSignature { count    = erased
                         , flags    = [Invertible]
                         , name     = NoFC n
                         , isData   = True
                         , type     = namePis 0 ty
                         }
getSig _ = Nothing

------------------------------------------------------------------------
-- Declaration

record Declaration where
  constructor MkDeclaration
  name   : Name
  count  : RigCount
  flags  : List FnOpt
  isData : Bool
  type   : RawImp

sigToDecl : Signature -> Declaration
sigToDecl sig = MkDeclaration
  { name = sig.name.val
  , count = sig.count
  , flags = sig.flags
  , isData = sig.isData
  , type = sig.type
  }

------------------------------------------------------------------------


-- TODO: Check all the parts of the body are legal
-- TODO: Deal with default superclass implementations

mkDataTy : FC -> List (Name, (RigCount, RawImp)) -> RawImp
mkDataTy fc [] = IType fc
mkDataTy fc ((n, (_, ty)) :: ps)
    = IPi fc top Explicit (Just n) ty (mkDataTy fc ps)

jname : (Name, (RigCount, RawImp)) -> (Maybe Name, RigCount, RawImp)
jname (n, rig, t) = (Just n, rig, t)

mkTy : FC -> PiInfo RawImp ->
       List (Maybe Name, RigCount, RawImp) -> RawImp -> RawImp
mkTy fc imp [] ret = ret
mkTy fc imp ((n, c, argty) :: args) ret
    = IPi fc c imp n argty (mkTy fc imp args ret)

mkIfaceData : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              FC -> WithDefault Visibility Private -> Env Term vars ->
              List (Maybe Name, RigCount, RawImp) ->
              Name -> Name -> List (Name, (RigCount, RawImp)) ->
              Maybe (List1 Name) -> List (Name, RigCount, RawImp) -> Core ImpDecl
mkIfaceData {vars} ifc def_vis env constraints n conName ps dets meths
    = let opts = [NoHints, UniqueSearch] ++
                 maybe [] (singleton . SearchBy) dets
          pNames = map fst ps
          retty = apply (IVar vfc n) (map (IVar EmptyFC) pNames)
          conty = mkTy vfc Implicit (map jname ps) $
                  mkTy vfc AutoImplicit (map bhere constraints) $
                  mkTy vfc Explicit (map bname meths) retty
          con = MkImpTy vfc (NoFC conName) !(bindTypeNames ifc [] (pNames ++ map fst meths ++ toList vars) conty)
          bound = pNames ++ map fst meths ++ toList vars in

          pure $ IData vfc def_vis Nothing {- ?? -}
               $ MkImpData vfc n
                   (Just !(bindTypeNames ifc [] bound (mkDataTy vfc ps)))
                   opts [con]
  where
    vfc : FC
    vfc = virtualiseFC ifc

    bname : (Name, RigCount, RawImp) -> (Maybe Name, RigCount, RawImp)
    bname (n, c, t) = (Just n, c, IBindHere (getFC t) (PI erased) t)

    bhere : (Maybe Name, RigCount, RawImp) -> (Maybe Name, RigCount, RawImp)
    bhere (n, c, t) = (n, c, IBindHere (getFC t) (PI erased) t)

-- Get the implicit arguments for a method declaration or constraint hint
-- to allow us to build the data declaration
getMethDecl : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Env Term vars -> NestedNames vars ->
              (params : List (Name, (RigCount, RawImp))) ->
              (mnames : List Name) ->
              (RigCount, nm, RawImp) ->
              Core (nm, RigCount, RawImp)
getMethDecl {vars} env nest params mnames (c, nm, ty)
    = do let paramNames = map fst params
         ty_imp <- bindTypeNames EmptyFC [] (paramNames ++ mnames ++ toList vars) ty
         pure (nm, c, stripParams paramNames ty_imp)
  where
    -- We don't want the parameters to explicitly appear in the method
    -- type in the record for the interface (they are parameters of the
    -- interface type), so remove it here
    stripParams : List Name -> RawImp -> RawImp
    stripParams ps (IPi fc r p mn arg ret)
        = if (maybe False (\n => n `elem` ps) mn)
             then stripParams ps ret
             else IPi fc r p mn arg (stripParams ps ret)
    stripParams ps ty = ty

-- bind the auto implicit for the interface - put it first, as it may be needed
-- in other method variables, including implicit variables
bindIFace : FC -> RawImp -> RawImp -> RawImp
bindIFace fc ity sc = IPi fc top AutoImplicit (Just (UN $ Basic "__con")) ity sc

-- Get the top level function for implementing a method
getMethToplevel : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  Env Term vars -> Visibility ->
                  Name -> Name ->
                  (constraints : List (Maybe Name)) ->
                  (allmeths : List Name) ->
                  (params : List (Name, (RigCount, RawImp))) ->
                  Signature ->
                  Core (List ImpDecl)
getMethToplevel {vars} env vis iname cname constraints allmeths params sig
    = do let paramNames = map fst params
         let ity = apply (IVar vfc iname) (map (IVar EmptyFC) paramNames)
         -- Make the constraint application explicit for any method names
         -- which appear in other method types
         let ty_constr =
             substNames (toList vars) (map applyCon allmeths) sig.type
         ty_imp <- bindTypeNames EmptyFC [] (toList vars) (bindPs params $ bindIFace vfc ity ty_constr)
         cn <- traverseFC inCurrentNS sig.name
         let tydecl = IClaim (MkFCVal vfc $ MkIClaimData sig.count vis (if sig.isData then [Inline, Invertible]
                                            else [Inline])
                                      (MkImpTy vfc cn ty_imp))
         let conapp = apply (IVar vfc cname)
                            (map (IBindVar EmptyFC) (map bindName allmeths))
         let argns = getExplicitArgs 0 sig.type
         -- eta expand the RHS so that we put implicits in the right place
         let fnclause = PatClause vfc
                                  (INamedApp vfc
                                             (IVar cn.fc cn.val) -- See #3409
                                             (UN $ Basic "__con")
                                             conapp
                                             )
                                  (mkLam argns
                                    (apply (IVar EmptyFC (methName sig.name.val))
                                           (map (IVar EmptyFC) argns)))
         let fndef = IDef vfc cn.val [fnclause]
         pure [tydecl, fndef]
  where
    vfc : FC
    vfc = virtualiseFC sig.name.fc

    -- Bind the type parameters given explicitly - there might be information
    -- in there that we can't infer after all
    bindPs : List (Name, (RigCount, RawImp)) -> RawImp -> RawImp
    bindPs [] ty = ty
    bindPs ((n, rig, pty) :: ps) ty
        = IPi (getFC pty) rig Implicit (Just n) pty (bindPs ps ty)

    applyCon : Name -> (Name, RawImp)
    applyCon n = let name = UN (Basic "__con") in
                 (n, INamedApp vfc (IVar vfc n) name (IVar vfc name))

    getExplicitArgs : Int -> RawImp -> List Name
    getExplicitArgs i (IPi _ _ Explicit n _ sc)
        = MN "arg" i :: getExplicitArgs (i + 1) sc
    getExplicitArgs i (IPi _ _ _ n _ sc) = getExplicitArgs i sc
    getExplicitArgs i tm = []

    mkLam : List Name -> RawImp -> RawImp
    mkLam [] tm = tm
    mkLam (x :: xs) tm
       = ILam EmptyFC top Explicit (Just x) (Implicit vfc False) (mkLam xs tm)

    bindName : Name -> String
    bindName (UN n) = "__bind_" ++ displayUserName n
    bindName (NS _ n) = bindName n
    bindName n = show n

    methName : Name -> Name
    methName n = UN (Basic $ bindName n)

-- Get the function for chasing a constraint. This is one of the
-- arguments to the record, appearing before the method arguments.
getConstraintHint : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    FC -> Env Term vars -> Visibility ->
                    Name -> Name ->
                    (constraints : List Name) ->
                    (allmeths : List Name) ->
                    (params : List (Name, RigCount, RawImp)) ->
                    (Name, RawImp) -> Core (Name, List ImpDecl)
getConstraintHint {vars} fc env vis iname cname constraints meths params (cn, con)
    = do let pNames = map fst params
         let ity = apply (IVar fc iname) (map (IVar fc) pNames)
         let fty = mkTy fc Implicit (map jname params) $
                   mkTy fc Explicit [(Nothing, top, ity)] con
         ty_imp <- bindTypeNames fc [] (pNames ++ meths ++ toList vars) fty
         let hintname = DN ("Constraint " ++ show con)
                          (UN (Basic $ "__" ++ show iname ++ "_" ++ show con))

         let tydecl = IClaim (MkFCVal fc $ MkIClaimData top vis [Inline, Hint False]
                          (MkImpTy EmptyFC (NoFC hintname) ty_imp))

         let conapp = apply (impsBind (IVar fc cname) (map bindName constraints))
                              (map (const (Implicit fc True)) meths)

         let fnclause = PatClause fc (IApp fc (IVar fc hintname) conapp)
                                  (IVar fc (constName cn))
         let fndef = IDef fc hintname [fnclause]
         pure (hintname, [tydecl, fndef])
  where
    bindName : Name -> String
    bindName (UN n) = "__bind_" ++ displayUserName n
    bindName (NS _ n) = bindName n
    bindName n = show n

    constName : Name -> Name
    constName n = UN (Basic $ bindName n)

    impsBind : RawImp -> List String -> RawImp
    impsBind fn [] = fn
    impsBind fn (n :: ns)
        = impsBind (IAutoApp fc fn (IBindVar fc n)) ns


getDefault : ImpDecl -> Maybe (FC, List FnOpt, Name, List ImpClause)
getDefault (IDef fc n cs) = Just (fc, [], n, cs)
getDefault _ = Nothing

mkCon : FC -> Name -> Name
mkCon loc (NS ns (UN n))
   = let str = displayUserName n in
     NS ns (DN (str ++ " at " ++ show loc) (UN $ Basic ("__mk" ++ str)))
mkCon loc n
   = let str = show n in
     DN (str ++ " at " ++ show loc) (UN $ Basic ("__mk" ++  str))

updateIfaceSyn : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 Name -> Name -> List Name -> List Name -> List RawImp ->
                 List Declaration -> List (Name, List ImpClause) ->
                 Core ()
updateIfaceSyn iname cn impps ps cs ms ds
    = do ms' <- traverse totMeth ms
         let info = MkIFaceInfo cn impps ps cs ms' ds
         update Syn { ifaces     $= addName iname info,
                      saveIFaces $= (iname :: ) }
 where
    totMeth : Declaration -> Core Method
    totMeth decl
        = do let treq = findTotality decl.flags
             pure $ MkMethod { name = decl.name
                             , count = decl.count
                             , totalReq = treq
                             , type = decl.type
                             }

-- Read the implicitly added parameters from an interface type, so that we
-- know to substitute an implicit in when defining the implementation
getImplParams : Term vars -> List Name
getImplParams (Bind _ n (Pi _ _ Implicit _) sc)
    = n :: getImplParams sc
getImplParams _ = []

export
elabInterface : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto m : Ref MD Metadata} ->
                {auto o : Ref ROpts REPLOpts} ->
                FC -> WithDefault Visibility Private ->
                Env Term vars -> NestedNames vars ->
                (constraints : List (Maybe Name, RawImp)) ->
                Name ->
                (params : List (Name, (RigCount, RawImp))) ->
                (dets : Maybe (List1 Name)) ->
                (conName : Maybe (String, Name)) ->
                List ImpDecl ->
                Core ()
elabInterface {vars} ifc def_vis env nest constraints iname params dets mcon body
    = do fullIName <- getFullName iname
         ns_iname <- inCurrentNS fullIName
         let conName_in = maybe (mkCon vfc fullIName) snd mcon
         -- Machine generated names need to be qualified when looking them up
         conName <- inCurrentNS conName_in
         whenJust (fst <$> mcon) (addDocString conName)
         let meth_sigs = mapMaybe getSig body
         let meth_decls = map sigToDecl meth_sigs
         let meth_names = map name meth_decls
         let defaults = mapMaybe getDefault body

         elabAsData conName meth_names meth_sigs
         elabConstraintHints conName meth_names
         elabMethods conName meth_names meth_sigs
         ds <- traverse (elabDefault meth_decls) defaults

         ns_meths <- traverse (\mt => do n <- inCurrentNS mt.name
                                         pure ({ name := n } mt)) meth_decls
         defs <- get Ctxt
         Just ty <- lookupTyExact ns_iname (gamma defs)
              | Nothing => undefinedName ifc iname
         let implParams = getImplParams ty

         updateIfaceSyn ns_iname conName
                        implParams paramNames (map snd constraints)
                        ns_meths ds
  where
    vfc : FC
    vfc = virtualiseFC ifc

    paramNames : List Name
    paramNames = map fst params

    nameCons : Int -> List (Maybe Name, RawImp) -> List (Name, RawImp)
    nameCons i [] = []
    nameCons i ((_, ty) :: rest)
        = (UN (Basic $ "__con" ++ show i), ty) :: nameCons (i + 1) rest

    -- Elaborate the data declaration part of the interface
    elabAsData : (conName : Name) -> List Name ->
                 List Signature ->
                 Core ()
    elabAsData conName meth_names meth_sigs
        = do -- set up the implicit arguments correctly in the method
             -- signatures and constraint hints
             meths <- traverse (\ meth => getMethDecl env nest params meth_names
                                          (meth.count, meth.name.val, meth.type))
                                meth_sigs
             log "elab.interface" 5 $ "Method declarations: " ++ show meths

             consts <- traverse (getMethDecl env nest params meth_names . (top,)) constraints
             log "elab.interface" 5 $ "Constraints: " ++ show consts

             dt <- mkIfaceData vfc def_vis env consts iname conName params
                                  dets meths
             log "elab.interface" 10 $ "Methods: " ++ show meths
             log "elab.interface" 5 $ "Making interface data type " ++ show dt
             ignore $ processDecls nest env [dt]

    elabMethods : (conName : Name) -> List Name ->
                  List Signature ->
                  Core ()
    elabMethods conName meth_names meth_sigs
        = do -- Methods have same visibility as data declaration
             fnsm <- traverse (getMethToplevel env (collapseDefault def_vis)
                                               iname conName
                                               (map fst constraints)
                                               meth_names
                                               params) meth_sigs
             let fns = concat fnsm
             log "elab.interface" 5 $ "Top level methods: " ++ show fns
             traverse_ (processDecl [] nest env) fns
             traverse_ (\n => do mn <- inCurrentNS n
                                 setFlag vfc mn Inline
                                 setFlag vfc mn TCInline
                                 setFlag vfc mn Overloadable) meth_names

    -- Check that a default definition is correct. We just discard it here once
    -- we know it's okay, since we'll need to re-elaborate it for each
    -- instance, to specialise it
    elabDefault : List Declaration ->
                  (FC, List FnOpt, Name, List ImpClause) ->
                  Core (Name, List ImpClause)
    elabDefault tydecls (dfc, opts, n, cs)
        = do -- orig <- branch

             let dn_in = MN ("Default implementation of " ++ show n) 0
             dn <- inCurrentNS dn_in

             (rig, dty) <-
                       case findBy (\ d => d <$ guard (n == d.name)) tydecls of
                          Just d => pure (d.count, d.type)
                          Nothing => throw (GenericMsg dfc ("No method named " ++ show n ++ " in interface " ++ show iname))

             let ity = apply (IVar vdfc iname) (map (IVar vdfc) paramNames)

             -- Substitute the method names with their top level function
             -- name, so they don't get implicitly bound in the name
             methNameMap <- traverse (\d =>
                                do let n = d.name
                                   cn <- inCurrentNS n
                                   pure (n, applyParams (IVar vdfc cn) paramNames))
                               tydecls
             let dty = bindPs params      -- bind parameters
                     $ bindIFace vdfc ity -- bind interface (?!)
                     $ substNames (toList vars) methNameMap dty

             dty_imp <- bindTypeNames dfc [] (map name tydecls ++ toList vars) dty
             log "elab.interface.default" 5 $ "Default method " ++ show dn ++ " : " ++ show dty_imp

             let dtydecl = IClaim $ MkFCVal vdfc
                                  $ MkIClaimData rig (collapseDefault def_vis) []
                                  $ MkImpTy EmptyFC (NoFC dn) dty_imp

             processDecl [] nest env dtydecl

             cs' <- traverse (changeName dn) cs
             log "elab.interface.default" 5 $ "Default method body " ++ show cs'

             processDecl [] nest env (IDef vdfc dn cs')
             -- Reset the original context, we don't need to keep the definition
             -- Actually we do for the metadata and name map!
--              put Ctxt orig
             pure (n, cs)
      where
        vdfc : FC
        vdfc = virtualiseFC dfc

        -- Bind the type parameters given explicitly - there might be information
        -- in there that we can't infer after all
        bindPs : List (Name, (RigCount, RawImp)) -> RawImp -> RawImp
        bindPs [] ty = ty
        bindPs ((n, (rig, pty)) :: ps) ty
          = IPi (getFC pty) rig Implicit (Just n) pty (bindPs ps ty)

        applyParams : RawImp -> List Name -> RawImp
        applyParams tm [] = tm
        applyParams tm (UN (Basic n) :: ns)
            = applyParams (INamedApp vdfc tm (UN (Basic n)) (IBindVar vdfc n)) ns
        applyParams tm (_ :: ns) = applyParams tm ns

        changeNameTerm : Name -> RawImp -> Core RawImp
        changeNameTerm dn (IVar fc n')
            = do if n /= n' then pure (IVar fc n') else do
                 log "ide-mode.highlight" 7 $
                   "elabDefault is trying to add Function: " ++ show n ++ " (" ++ show fc ++")"
                 whenJust (isConcreteFC fc) $ \nfc => do
                   log "ide-mode.highlight" 7 $ "elabDefault is adding Function: " ++ show n
                   addSemanticDecorations [(nfc, Function, Just n)]
                 pure (IVar fc dn)
        changeNameTerm dn (IApp fc f arg)
            = IApp fc <$> changeNameTerm dn f <*> pure arg
        changeNameTerm dn (IAutoApp fc f arg)
            = IAutoApp fc <$> changeNameTerm dn f <*> pure arg
        changeNameTerm dn (INamedApp fc f x arg)
            = INamedApp fc <$> changeNameTerm dn f <*> pure x <*> pure arg
        changeNameTerm dn tm = pure tm

        changeName : Name -> ImpClause -> Core ImpClause
        changeName dn (PatClause fc lhs rhs)
            = PatClause fc <$> changeNameTerm dn lhs <*> pure rhs
        changeName dn (WithClause fc lhs rig wval prf flags cs)
            = WithClause fc
                 <$> changeNameTerm dn lhs
                 <*> pure rig
                 <*> pure wval
                 <*> pure prf
                 <*> pure flags
                 <*> traverse (changeName dn) cs
        changeName dn (ImpossibleClause fc lhs)
            = ImpossibleClause fc <$> changeNameTerm dn lhs

    elabConstraintHints : (conName : Name) -> List Name ->
                          Core ()
    elabConstraintHints conName meth_names
        = do let nconstraints = nameCons 0 constraints
             chints <- traverse (getConstraintHint vfc env (collapseDefault def_vis)
                                                 iname conName
                                                 (map fst nconstraints)
                                                 meth_names
                                                 params) nconstraints
             log "elab.interface" 5 $ "Constraint hints from " ++ show constraints ++ ": " ++ show chints
             Core.Core.traverse_ (processDecl [] nest env) (concatMap snd chints)
             traverse_ (\n => do mn <- inCurrentNS n
                                 setFlag vfc mn TCInline) (map fst chints)
