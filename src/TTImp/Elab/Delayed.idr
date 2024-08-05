module TTImp.Elab.Delayed

import Core.Case.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check

import Libraries.Data.IntMap
import Libraries.Data.NameMap
import Data.List

%default covering

-- We run the elaborator in the given environment, but need to end up with a
-- closed term.
mkClosedElab : {vars : _} ->
               FC -> Env Term vars ->
               (Core (Term vars, Glued vars)) ->
               Core ClosedTerm
mkClosedElab fc [] elab
    = do (tm, _) <- elab
         pure tm
mkClosedElab {vars = x :%: vars} fc (b :: env) elab
    = mkClosedElab fc env
          (do (sc', _) <- elab
              let b' = newBinder b
              pure (Bind fc x b' sc', gErased fc))
  where
    -- in 'abstractEnvType' we get a Pi binder (so we'll need a Lambda) for
    -- everything except 'Let', so make the appropriate corresponding binder
    -- here
    newBinder : Binder (Term vars) -> Binder (Term vars)
    newBinder b@(Let _ _ _ _) = b
    newBinder b = Lam (binderLoc b) (multiplicity b) Explicit (binderType b)

deeper : {auto e : Ref EST (EState vars)} ->
         Core a -> Core a
deeper elab
    = do est <- get EST
         let d = delayDepth est
         put EST ({ delayDepth := 1 + d } est)
         res <- elab
         est <- get EST
         put EST ({ delayDepth := d } est)
         pure res

-- Try the given elaborator; if it fails, and the error matches the
-- predicate, make a hole and try it again later when more holes might
-- have been resolved
export
delayOnFailure : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 FC -> RigCount -> Env Term vars ->
                 (expected : Maybe (Glued vars)) ->
                 (Error -> Bool) ->
                 (pri : DelayReason) ->
                 (Bool -> Core (Term vars, Glued vars)) ->
                 Core (Term vars, Glued vars)
delayOnFailure fc rig env exp pred pri elab
    = do ust <- get UST
         let nos = noSolve ust -- remember the holes we shouldn't solve
         handle (elab False)
          (\err =>
              do est <- get EST
                 expected <- mkExpected exp
                 if pred err
                    then
                      do nm <- genName "delayed"
                         (ci, dtm) <- newDelayed fc linear env nm !(getTerm expected)
                         logGlueNF "elab.delay" 5 ("Postponing elaborator " ++ show nm ++
                                      " at " ++ show fc ++
                                      " for") env expected
                         log "elab.delay" 10 ("Due to error " ++ show err)
                         defs <- get Ctxt
                         update UST { delayedElab $=
                                 ((pri, ci, localHints defs,
                                   mkClosedElab fc env
                                      (deeper
                                        (do ust <- get UST
                                            let nos' = noSolve ust
                                            put UST ({ noSolve := nos } ust)
                                            res <- elab True
                                            ust <- get UST
                                            put UST ({ noSolve := nos' } ust)
                                            pure res))) :: ) }
                         pure (dtm, expected)
                    else throw err)
  where
    mkExpected : Maybe (Glued vars) -> Core (Glued vars)
    mkExpected (Just ty) = pure ty
    mkExpected Nothing
        = do nm <- genName "delayTy"
             u <- uniVar fc
             ty <- metaVar fc erased env nm (TType fc u)
             pure (gnf env ty)

export
delayElab : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            FC -> RigCount -> Env Term vars ->
            (expected : Maybe (Glued vars)) ->
            (pri : DelayReason) ->
            Core (Term vars, Glued vars) ->
            Core (Term vars, Glued vars)
delayElab {vars} fc rig env exp pri elab
    = do ust <- get UST
         let nos = noSolve ust -- remember the holes we shouldn't solve
         nm <- genName "delayed"
         expected <- mkExpected exp
         (ci, dtm) <- newDelayed fc linear env nm !(getTerm expected)
         logGlueNF "elab.delay" 5 ("Postponing elaborator " ++ show nm ++
                      " for") env expected
         defs <- get Ctxt
         update UST { delayedElab $=
                 ((pri, ci, localHints defs, mkClosedElab fc env
                                              (do ust <- get UST
                                                  let nos' = noSolve ust
                                                  put UST ({ noSolve := nos } ust)
                                                  res <- elab
                                                  ust <- get UST
                                                  put UST ({ noSolve := nos' } ust)
                                                  pure res)) :: ) }
         pure (dtm, expected)
  where
    mkExpected : Maybe (Glued vars) -> Core (Glued vars)
    mkExpected (Just ty) = pure ty
    mkExpected Nothing
        = do nm <- genName "delayTy"
             u <- uniVar fc
             ty <- metaVar fc erased env nm (TType fc u)
             pure (gnf env ty)

export
ambiguous : Error -> Bool
ambiguous (AmbiguousElab _ _ _) = True
ambiguous (AmbiguousName _ _) = True
ambiguous (AmbiguityTooDeep _ _ _) = True
ambiguous (InType _ _ err) = ambiguous err
ambiguous (InCon _ err) = ambiguous err
ambiguous (InLHS _ _ err) = ambiguous err
ambiguous (InRHS _ _ err) = ambiguous err
ambiguous (WhenUnifying _ _ _ _ _ err) = ambiguous err
ambiguous _ = False

mutual
  mismatchNF : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
  mismatchNF defs (NTCon _ xn xt _ xargs) (NTCon _ yn yt _ yargs)
      = if xn /= yn
           then pure True
           else anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
  mismatchNF defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
      = if xt /= yt
           then pure True
           else anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
  mismatchNF defs (NPrimVal _ xc) (NPrimVal _ yc) = pure (xc /= yc)
  mismatchNF defs (NDelayed _ _ x) (NDelayed _ _ y) = mismatchNF defs x y
  mismatchNF defs (NDelay _ _ _ x) (NDelay _ _ _ y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)
  mismatchNF _ _ _ = pure False

  mismatch : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Defs -> (Closure vars, Closure vars) -> Core Bool
  mismatch defs (x, y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)

contra : {auto c : Ref Ctxt Defs} ->
         {vars : _} ->
         Defs -> NF vars -> NF vars -> Core Bool
-- Unlike 'impossibleOK', any mismatch indicates an unrecoverable error
contra defs (NTCon _ xn xt xa xargs) (NTCon _ yn yt ya yargs)
    = if xn /= yn
         then pure True
         else anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
contra defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
contra defs (NPrimVal _ x) (NPrimVal _ y) = pure (x /= y)
contra defs (NDCon _ _ _ _ _) (NPrimVal _ _) = pure True
contra defs (NPrimVal _ _) (NDCon _ _ _ _ _) = pure True
contra defs x y = pure False

-- Errors that might be recoverable later if we try again. Generally -
-- ambiguity errors, type inference errors
export
recoverable : {auto c : Ref Ctxt Defs} ->
              Error -> Core Bool
recoverable (CantConvert _ gam env l r)
   = do defs <- get Ctxt
        let defs = { gamma := gam } defs
        pure $ not !(contra defs !(nf defs env l) !(nf defs env r))
recoverable (CantSolveEq _ gam env l r)
   = do defs <- get Ctxt
        let defs = { gamma := gam } defs
        pure $ not !(contra defs !(nf defs env l) !(nf defs env r))
recoverable (UndefinedName _ _) = pure False
recoverable (LinearMisuse _ _ _ _) = pure False
recoverable (InType _ _ err) = recoverable err
recoverable (InCon _ err) = recoverable err
recoverable (InLHS _ _ err) = recoverable err
recoverable (InRHS _ _ err) = recoverable err
recoverable (WhenUnifying _ _ _ _ _ err) = recoverable err
recoverable _ = pure True

data RetryError
     = RecoverableErrors
     | AllErrors

Show RetryError where
  show RecoverableErrors = "RecoverableErrors"
  show AllErrors = "AllErrors"

-- Try all the delayed elaborators. If there's a failure, we want to
-- show the ambiguity errors first (since that's the likely cause)
-- Return all the ones that need trying again
retryDelayed' : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto e : Ref EST (EState vars)} ->
                RetryError ->
                (progress : Bool) ->
                List (DelayReason, Int, NameMap (), Core ClosedTerm) ->
                List (DelayReason, Int, NameMap (), Core ClosedTerm) ->
                Core (Bool, List (DelayReason, Int, NameMap (), Core ClosedTerm))
retryDelayed' errmode p acc [] = pure (p, reverse acc)
retryDelayed' errmode p acc (d@(_, i, hints, elab) :: ds)
    = do defs <- get Ctxt
         Just Delayed <- lookupDefExact (Resolved i) (gamma defs)
              | _ => retryDelayed' errmode p acc ds
         handle
           (do est <- get EST
               logC "elab.retry" 5 $ do pure $ show (delayDepth est) ++ ": Retrying delayed hole " ++ show !(getFullName (Resolved i))
               -- elab itself might have delays internally, so keep track of them
               update UST { delayedElab := [] }
               update Ctxt { localHints := hints }

               tm <- elab
               ust <- get UST
               let ds' = reverse (delayedElab ust) ++ ds

               updateDef (Resolved i) (const (Just
                    (PMDef (MkPMDefInfo NotHole True False)
                           SLNil (STerm 0 tm) (STerm 0 tm) [])))
               logTerm "elab.update" 5 ("Resolved delayed hole " ++ show i) tm
               logTermNF "elab.update" 5 ("Resolved delayed hole NF " ++ show i) [] tm
               removeHole i
               retryDelayed' errmode True acc ds')
           (\err => do logC "elab" 5 $ do pure $ show errmode ++ ":Error in " ++ show !(getFullName (Resolved i))
                                              ++ "\n" ++ show err
                       case errmode of
                         RecoverableErrors =>
                            if not !(recoverable err)
                               then throw err
                               else retryDelayed' errmode p (d :: acc) ds
                         AllErrors =>
                            -- we've got an error, but see if we get a more
                            -- helpful one with a later elaborator
                            handle (do ignore $ retryDelayed' errmode p [] ds
                                       throw err)
                               (\err' => throw (better err err')))
  where
    better : Error -> Error -> Error
    better e (GenericMsg _ _) = e
    better (GenericMsg _ _) e = e
    better e _ = e

export
retryDelayed : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               UnifyInfo -> List (DelayReason, Int, NameMap (), Core ClosedTerm) ->
               Core ()
retryDelayed mode ds
    = do (p, ds) <- retryDelayed' RecoverableErrors False [] ds -- try everything again
         solveConstraints mode Normal -- maybe we can resolve some interfaces now
         if p
            then retryDelayed mode ds -- progress, go around again
            else ignore $ retryDelayed' AllErrors False [] ds -- fail on all errors

-- Run an elaborator, then all the delayed elaborators arising from it
export
runDelays : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            (DelayReason -> Bool) -> Core a -> Core a
runDelays pri elab
    = do ust <- get UST
         let olddelayed = delayedElab ust
         put UST ({ delayedElab := [] } ust)
         tm <- elab
         ust <- get UST
         log "elab.delay" 2 $ "Rerunning delayed in elaborator"
         handle (do ignore $ retryDelayed' AllErrors False []
                       (reverse (filter hasPri (delayedElab ust))))
                (\err => do put UST ({ delayedElab := olddelayed } ust)
                            throw err)
         update UST { delayedElab $= (++ olddelayed) }
         pure tm
  where
    hasPri : (DelayReason, d) -> Bool
    hasPri (n, _) = pri n
