module TTImp.ProcessType

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Hash
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Elab
import TTImp.ProcessFnOpt
import TTImp.TTImp

import Data.List
import Data.List1
import Data.String
import Libraries.Data.NameMap
import Libraries.Data.StringMap
import Libraries.Data.WithDefault

%default covering
export
getFnString : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
               RawImp -> Core String
getFnString (IPrimVal _ (Str st)) = pure st
getFnString tm
    = do inidx <- resolveName (UN $ Basic "[foreign]")
         let fc = getFC tm
         let gstr = gnf [<] (PrimVal fc $ PrT StringType)
         etm <- checkTerm inidx InExpr [] (MkNested []) [<] tm gstr
         defs <- get Ctxt
         case !(nf defs [<] etm) of
              NPrimVal fc (Str st) => pure st
              _ => throw (GenericMsg fc "%foreign calling convention must evaluate to a String")

-- If it's declared as externally defined, set the definition to
-- ExternFn <arity>, where the arity is assumed to be fixed (i.e.
-- not dependent on any of the arguments)
-- Similarly set foreign definitions. Possibly combine these?
initDef : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          FC -> Name -> Env Term vars -> Term vars -> List FnOpt -> Core Def
initDef fc n env ty []
    = do addUserHole False n
         pure None
initDef fc n env ty (ExternFn :: opts)
    = do defs <- get Ctxt
         a <- getArity defs env ty
         pure (ExternDef a)
initDef fc n env ty (ForeignFn cs :: opts)
    = do defs <- get Ctxt
         a <- getArity defs env ty
         cs' <- traverse getFnString cs
         pure (ForeignDef a cs')
-- In this case, nothing to initialise to, but we do need to process the
-- calling conventions then process the rest of the options.
-- This means, for example, we can technically re-export something foreign!
-- I suppose that may be useful one day...
initDef fc n env ty (ForeignExport cs :: opts)
    = do cs' <- traverse getFnString cs
         conv <- traverse getConvention cs'
         defs <- get Ctxt
         put Ctxt ({ foreignExports $= insert n conv } defs)
         initDef fc n env ty opts
  where
    getConvention : String -> Core (String, String)
    getConvention c
        = do let (lang ::: fname :: []) = split (== ':') c
                 | _ => throw (GenericMsg fc "Invalid calling convention")
             pure (trim lang, trim fname)
initDef fc n env ty (_ :: opts) = initDef fc n env ty opts

-- Find the inferrable argument positions in a type. This is useful for
-- generalising partially evaluated definitions and (potentially) in interactive
-- editing
findInferrable : {auto c : Ref Ctxt Defs} ->
                 Defs -> NF [<] -> Core (List Nat)
findInferrable defs ty = fi 0 0 [] [] ty
  where
    mutual
      -- Add to the inferrable arguments from the given type. An argument is
      -- inferrable if it's guarded by a constructor, or on its own
      findInf : List Nat -> List (Name, Nat) ->
                NF [<] -> Core (List Nat)
      findInf acc pos (NApp _ (NRef Bound n) [<])
          = case lookup n pos of
                 Nothing => pure acc
                 Just p => if p `elem` acc then pure acc else pure (p :: acc)
      findInf acc pos (NDCon _ _ _ _ args)
          = do args' <- traverse (evalClosure defs . snd) (toList args)
               findInfs acc pos args'
      findInf acc pos (NTCon _ _ _ _ args)
          = do args' <- traverse (evalClosure defs . snd) (toList args)
               findInfs acc pos args'
      findInf acc pos (NDelayed _ _ t) = findInf acc pos t
      findInf acc _ _ = pure acc

      findInfs : List Nat -> List (Name, Nat) -> List (NF [<]) -> Core (List Nat)
      findInfs acc pos [] = pure acc
      findInfs acc pos (n :: ns) = findInf !(findInfs acc pos ns) pos n

    fi : Nat -> Int -> List (Name, Nat) -> List Nat -> NF [<] -> Core (List Nat)
    fi pos i args acc (NBind fc x (Pi _ _ _ aty) sc)
        = do let argn = MN "inf" i
             sc' <- sc defs (toClosure defaultOpts [<] (Ref fc Bound argn))
             acc' <- findInf acc args !(evalClosure defs aty)
             rest <- fi (1 + pos) (1 + i) ((argn, pos) :: args) acc' sc'
             pure rest
    fi pos i args acc ret = findInf acc args ret

checkForShadowing : (env : StringMap FC) -> RawImp -> List (String, FC, FC)
checkForShadowing env (IPi fc _ _ (Just (UN (Basic name))) argTy retTy) =
    let argShadowing = checkForShadowing empty argTy
     in (case lookup name env of
        Just origFc => (name, origFc, fc) :: checkForShadowing env retTy
        Nothing => checkForShadowing (insert name fc env) retTy)
        ++ argShadowing
checkForShadowing env t = []

export
processType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              List ElabOpt -> NestedNames vars -> Env Term vars ->
              FC -> RigCount -> Visibility ->
              List FnOpt -> ImpTy -> Core ()
processType {vars} eopts nest env fc rig vis opts (MkImpTy tfc n_in ty_raw)
    = do n <- inCurrentNS n_in.val

         addNameLoc n_in.fc n

         log "declare.type" 1 $ "Processing " ++ show n
         log "declare.type" 5 $ unwords ["Checking type decl:", show rig, show n, ":", show ty_raw]
         idx <- resolveName n

         -- Check 'n' is undefined
         defs <- get Ctxt
         Nothing <- lookupCtxtExact (Resolved idx) (gamma defs)
              | Just gdef => throw (AlreadyDefined fc n)

         u <- uniVar fc
         ty <-
             wrapErrorC eopts (InType fc n) $
                   checkTerm idx InType (HolesOkay :: eopts) nest env
                             (IBindHere fc (PI erased) ty_raw)
                             (gType fc u)
         logTermNF "declare.type" 3 ("Type of " ++ show n) [<] (abstractFullEnvType tfc env ty)

         def <- initDef fc n env ty opts
         let fullty = abstractFullEnvType tfc env ty

         (erased, dterased) <- findErased fullty
         defs <- get Ctxt
         empty <- clearDefs defs
         infargs <- findInferrable empty !(nf defs [<] fullty)

         ignore $ addDef (Resolved idx)
                ({ eraseArgs := erased,
                   safeErase := dterased,
                   inferrable := infargs }
                 (newDef fc n rig vars fullty (specified vis) def))
         -- Flag it as checked, because we're going to check the clauses
         -- from the top level.
         -- But, if it's a case block, it'll be checked as part of the top
         -- level check so don't set the flag.
         unless (InCase `elem` eopts) $ setLinearCheck idx True

         log "declare.type" 2 $ "Setting options for " ++ show n ++ ": " ++ show opts
         let name = Resolved idx
         let isNested : Name -> Bool
             isNested (Nested _ _) = True
             isNested (NS _ n) = isNested n
             isNested _ = False
         let nested = not (isNested n)
         traverse_ (processFnOpt fc (not (isNested n)) name) opts
         -- If no function-specific totality pragma has been used, attach the default totality
         unless (any isTotalityReq opts) $
           setFlag fc name (SetTotal !getDefaultTotalityOption)

         -- Add to the interactive editing metadata
         addTyDecl fc (Resolved idx) env ty -- for definition generation

         log "metadata.names" 7 $ "processType is adding ↓"
         addNameType n_in.fc (Resolved idx) env ty -- for looking up types

         traverse_ addToSave (keys (getMetas ty))
         addToSave n
         log "declare.type" 10 $ "Saving from " ++ show n ++ ": " ++ show (keys (getMetas ty))

         when (vis /= Private) $
              do addHashWithNames n
                 addHashWithNames ty
                 log "module.hash" 15 "Adding hash for type with name \{show n}"

         when (showShadowingWarning !getSession) $
            whenJust (fromList (checkForShadowing StringMap.empty ty_raw))
                $ recordWarning . ShadowingLocalBindings fc
