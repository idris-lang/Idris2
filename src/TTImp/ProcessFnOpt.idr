module TTImp.ProcessFnOpt

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Value

import TTImp.TTImp

import Libraries.Data.NameMap

import Data.SnocList

getRetTy : Defs -> ClosedNF -> Core Name
getRetTy defs (NBind fc _ (Pi _ _ _ _) sc)
    = getRetTy defs !(sc defs (toClosure defaultOpts Env.empty (Erased fc Placeholder)))
getRetTy defs (NTCon _ n _ _ _) = pure n
getRetTy defs ty
    = throw (GenericMsg (getLoc ty)
             "Can only add hints for concrete return types")

%inline
throwIf : {auto c : Ref Ctxt Defs} -> FC -> Bool -> String -> Core ()
throwIf fc cond msg = when cond $ throw (GenericMsg fc msg)

%inline
throwIfHasFlag : {auto c : Ref Ctxt Defs} -> FC -> Name -> DefFlag -> String -> Core ()
throwIfHasFlag fc ndef fl msg = throwIf fc !(hasFlag fc ndef fl) msg

%inline
throwIfHasTotality : {auto c : Ref Ctxt Defs} -> FC -> Name -> String -> Core ()
throwIfHasTotality fc ndef msg = throwIf fc !(hasSetTotal fc ndef) msg

export
processFnOpt : {auto c : Ref Ctxt Defs} ->
               FC -> Bool -> -- ^ top level name?
               Name -> FnOpt -> Core ()
processFnOpt fc _ ndef Unsafe
    = do setIsEscapeHatch fc ndef
processFnOpt fc _ ndef Inline
    = do throwIfHasFlag fc ndef NoInline "%noinline and %inline are mutually exclusive"
         setFlag fc ndef Inline
processFnOpt fc _ ndef NoInline
    = do throwIfHasFlag fc ndef Inline "%inline and %noinline are mutually exclusive"
         setFlag fc ndef NoInline
processFnOpt fc _ ndef Deprecate
    = setFlag fc ndef Deprecate
processFnOpt fc _ ndef TCInline
    = setFlag fc ndef TCInline
processFnOpt fc True ndef (Hint d)
    = do defs <- get Ctxt
         Just ty <- lookupTyExact ndef (gamma defs)
              | Nothing => undefinedName fc ndef
         target <- getRetTy defs !(nf defs Env.empty ty)
         addHintFor fc target ndef d False
processFnOpt fc _ ndef (Hint d)
    = do logC "elab" 5 $ do pure $ "Adding local hint " ++ show !(toFullNames ndef)
         addLocalHint ndef
processFnOpt fc True ndef (GlobalHint a)
    = addGlobalHint ndef a
processFnOpt fc _ ndef (GlobalHint True)
    = throw (GenericMsg fc "%defaulthint is not valid in local definitions")
processFnOpt fc _ ndef (GlobalHint False)
    = throw (GenericMsg fc "%globalhint is not valid in local definitions")
processFnOpt fc _ ndef ExternFn
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc _ ndef (ForeignFn _)
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc _ ndef (ForeignExport _)
    = pure ()
processFnOpt fc _ ndef Invertible
    = setFlag fc ndef Invertible
processFnOpt fc _ ndef (Totality tot)
    = do throwIfHasTotality fc ndef "Multiple totality modifiers"
         setFlag fc ndef (SetTotal tot)
processFnOpt fc _ ndef Macro
    = setFlag fc ndef Macro
processFnOpt fc _ ndef (SpecArgs ns)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact ndef (gamma defs)
              | Nothing => undefinedName fc ndef
         nty <- nf defs Env.empty (type gdef)
         ps <- getNamePos 0 nty
         ddeps <- collectDDeps nty
         specs <- collectSpec [] ddeps ps nty
         ignore $ addDef ndef ({ specArgs := specs } gdef)
  where
    insertDeps : List Nat -> List (Name, Nat) -> List Name -> List Nat
    insertDeps acc ps [] = acc
    insertDeps acc ps (n :: ns)
        = case lookup n ps of
               Nothing => insertDeps acc ps ns
               Just pos => if pos `elem` acc
                              then insertDeps acc ps ns
                              else insertDeps (pos :: acc) ps ns

    -- Collect the argument names which the dynamic args depend on
    collectDDeps : ClosedNF -> Core (List Name)
    collectDDeps (NBind tfc x (Pi _ _ _ nty) sc)
        = do defs <- get Ctxt
             empty <- clearDefs defs
             sc' <- sc defs (toClosure defaultOpts Env.empty (Ref tfc Bound x))
             if x `elem` ns
                then collectDDeps sc'
                else do aty <- quote empty Env.empty nty
                        -- Get names depended on by nty
                        let deps = keys (getRefs (UN Underscore) aty)
                        rest <- collectDDeps sc'
                        pure (rest ++ deps)
    collectDDeps _ = pure []

    -- Return names the type depends on, and whether it's a parameter
    mutual
      getDepsArgs : Bool -> SnocList ClosedNF -> NameMap Bool ->
                    Core (NameMap Bool)
      getDepsArgs inparam [<] ns = pure ns
      getDepsArgs inparam (as :< a) ns
          = do ns' <- getDeps inparam a ns
               getDepsArgs inparam as ns'

      getDeps : Bool -> ClosedNF -> NameMap Bool ->
                Core (NameMap Bool)
      getDeps inparam (NBind _ x (Pi _ _ _ pty) sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps inparam !(evalClosure defs pty) ns
               sc' <- sc defs (toClosure defaultOpts Env.empty (Erased fc Placeholder))
               getDeps inparam sc' ns'
      getDeps inparam (NBind _ x b sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps False !(evalClosure defs (binderType b)) ns
               sc' <- sc defs (toClosure defaultOpts Env.empty (Erased fc Placeholder))
               getDeps False sc' ns
      getDeps inparam (NApp _ (NRef Bound n) args) ns
          = do defs <- get Ctxt
               ns' <- getDepsArgs False !(traverse (evalClosure defs . snd) args) ns
               pure (insert n inparam ns')
      getDeps inparam (NDCon _ n t a args) ns
          = do defs <- get Ctxt
               getDepsArgs False !(traverse (evalClosure defs . snd) args) ns
      getDeps inparam (NTCon _ n t a args) ns
          = do defs <- get Ctxt
               params <- case !(lookupDefExact n (gamma defs)) of
                              Just (TCon _ _ ps _ _ _ _ _) => pure ps
                              _ => pure []
               let (ps, ds) = splitPs 0 params (map snd (toList args))
               ns' <- getDepsArgs True !(traverse (evalClosure defs) ps) ns
               getDepsArgs False !(traverse (evalClosure defs) ds) ns'
        where
          -- Split into arguments in parameter position, and others
          splitPs : Nat -> List Nat -> List ClosedClosure ->
                    (SnocList ClosedClosure, SnocList ClosedClosure)
          splitPs n params [] = ([<], [<])
          splitPs n params (x :: xs)
              = let (ps', ds') = splitPs (1 + n) params xs in
                    if n `elem` params
                       then (ps' :< x, ds')
                       else (ps', ds' :< x)
      getDeps inparam (NDelayed _ _ t) ns = getDeps inparam t ns
      getDeps inparams nf ns = pure ns

    -- If the name of an argument is in the list of specialisable arguments,
    -- record the position. Also record the position of anything the argument
    -- depends on which is only dependend on by declared static arguments.
    collectSpec : List Nat -> -- specialisable so far
                  List Name -> -- things depended on by dynamic args
                               -- We're assuming  it's a short list, so just use
                               -- List and don't worry about duplicates.
                  List (Name, Nat) -> ClosedNF -> Core (List Nat)
    collectSpec acc ddeps ps (NBind tfc x (Pi _ _ _ nty) sc)
        = do defs <- get Ctxt
             empty <- clearDefs defs
             sc' <- sc defs (toClosure defaultOpts Env.empty (Ref tfc Bound x))
             if x `elem` ns
                then do deps <- getDeps True !(evalClosure defs nty) NameMap.empty
                        -- Get names depended on by nty
                        -- Keep the ones which are either:
                        --  * parameters
                        --  * not depended on by a dynamic argument (the ddeps)
                        let rs = filter (\x => snd x ||
                                               not (fst x `elem` ddeps))
                                        (toList deps)
                        let acc' = insertDeps acc ps (x :: map fst rs)
                        collectSpec acc' ddeps ps sc'
                else collectSpec acc ddeps ps sc'
    collectSpec acc ddeps ps _ = pure acc

    getNamePos : Nat -> ClosedNF -> Core (List (Name, Nat))
    getNamePos i (NBind tfc x (Pi _ _ _ _) sc)
        = do defs <- get Ctxt
             ns' <- getNamePos (1 + i) !(sc defs (toClosure defaultOpts Env.empty (Erased tfc Placeholder)))
             pure ((x, i) :: ns')
    getNamePos _ _ = pure []
