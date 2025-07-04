module Core.Termination

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Value

import Core.Termination.CallGraph
import Core.Termination.Positivity
import Core.Termination.SizeChange

import Libraries.Data.NameMap

%default covering

-- Check if all branches end up as constructor arguments, with no other
-- function application, and set 'AllGuarded' if so.
-- This is to check whether a function can be considered a constructor form
-- for the sake of termination checking (and might have other uses...)
export
checkIfGuarded : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Core ()
checkIfGuarded fc n
    = do logC "totality.termination.guarded" 6 $ do pure $ "Check if Guarded: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just (PMDef _ _ _ _ pats) <- lookupDefExact n (gamma defs)
              | _ => pure ()
         t <- allGuarded pats
         when t $ setFlag fc n AllGuarded
  where
    guardedNF : {vars : _} -> Defs -> Env Term vars -> NF vars -> Core Bool
    guardedNF defs env (NDCon _ _ _ _ args) = pure True
    guardedNF defs env (NApp _ (NRef _ n) args)
        = do Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (AllGuarded `elem` flags gdef)
    guardedNF defs env _ = pure False

    checkNotFn : Defs -> Name -> Core Bool
    checkNotFn defs n
        = do Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             case definition gdef of
                  DCon _ _ _ => pure True
                  _ => pure (multiplicity gdef == erased
                              || (AllGuarded `elem` flags gdef))

    guarded : {vars : _} -> Env Term vars -> Term vars -> Core Bool
    guarded env tm
        = do defs <- get Ctxt
             empty <- clearDefs defs
             tmnf <- nf empty env tm
             if !(guardedNF defs env tmnf)
                then do Just gdef <- lookupCtxtExact n (gamma defs)
                             | Nothing => pure False
                        allM (checkNotFn defs) (keys (refersTo gdef))
                else pure False

    allGuarded : List (vs ** (Env Term vs, Term vs, Term vs)) -> Core Bool
    allGuarded [] = pure True
    allGuarded ((_ ** (env, lhs, rhs)) :: ps)
        = if !(guarded env rhs)
             then allGuarded ps
             else pure False

-- Check whether a function is terminating, and record in the context
export
checkTerminating : {auto c : Ref Ctxt Defs} ->
                   FC -> Name -> Core Terminating
checkTerminating loc n
    = do tot <- getTotality loc n
         logC "totality.termination" 6 $ do pure $ "Checking termination: " ++ show !(toFullNames n)
         case isTerminating tot of
              Unchecked =>
                 do tot' <- calcTerminating loc n
                    setTerminating loc n tot'
                    pure tot'
              t => pure t

-- Check whether a data type satisfies the strict positivity condition, and
-- record in the context
export
checkPositive : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Terminating
checkPositive loc n_in
    = do n <- toResolvedNames n_in
         tot <- getTotality loc n
         logC "totality.positivity" 6 $ do pure $ "Checking positivity: " ++ show !(toFullNames n)
         case isTerminating tot of
              Unchecked =>
                  do (tot', cons) <- calcPositive loc n
                     setTerminating loc n tot'
                     traverse_ (\c => setTerminating loc c tot') cons
                     pure tot'
              t => pure t


-- Check and record totality of the given name; positivity if it's a data
-- type, termination if it's a function
export
checkTotal : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Core Terminating
checkTotal loc n_in
    = do defs <- get Ctxt
         let Just nidx = getNameID n_in (gamma defs)
             | Nothing => undefinedName loc n_in
         let n = Resolved nidx
         tot <- getTotality loc n
         logC "totality" 5 $ do pure $ "Checking totality: " ++ show !(toFullNames n)
         defs <- get Ctxt
         case isTerminating tot of
              Unchecked => do
                  mgdef <- lookupCtxtExact n (gamma defs)
                  case definition <$> mgdef of
                       Just (TCon _ _ _ _ _ _ _)
                           => checkPositive loc n
                       _ => do whenJust (refersToM =<< mgdef) $ \ refs =>
                                 log "totality" 5 $ "  Mutually defined with:"
                                                 ++ show !(traverse toFullNames (keys refs))
                               checkTerminating loc n
              t => pure t
