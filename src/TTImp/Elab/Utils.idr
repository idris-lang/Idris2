module TTImp.Elab.Utils

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import TTImp.TTImp

detagSafe : Defs -> NF [] -> Core Bool
detagSafe defs (NTCon _ n _ _ args)
    = do Just (TCon _ _ _ _ _ _ _ (Just detags)) <- lookupDefExact n (gamma defs)
              | _ => pure False
         args' <- traverse (evalClosure defs) args
         pure $ notErased 0 detags args'
  where
    -- if any argument positions are in the detaggable set, and unerased, then
    -- detagging is safe
    notErased : Nat -> List Nat -> List (NF []) -> Bool
    notErased i [] _ = True -- Don't need an index available
    notErased i ns [] = False
    notErased i ns (NErased _ True :: rest)
        = notErased (i + 1) ns rest -- Can't detag here, look elsewhere
    notErased i ns (_ :: rest)
        = if i `elem` ns
             then True -- Safe to detag via this argument
             else notErased (i + 1) ns rest
detagSafe defs _ = pure False

findErasedFrom : Defs -> Nat -> NF [] -> Core (List Nat, List Nat)
findErasedFrom defs pos (NBind fc x (Pi c _ aty) scf)
    = do -- In the scope, use 'Erased fc True' to mean 'argument is erased'.
         -- It's handy here, because we can use it to tell if a detaggable
         -- argument position is available
         sc <- scf defs (toClosure defaultOpts [] (Erased fc (isErased c)))
         (erest, dtrest) <- findErasedFrom defs (1 + pos) sc
         let dt' = if !(detagSafe defs aty)
                      then (pos :: dtrest) else dtrest
         pure $ if isErased c
                   then (pos :: erest, dt')
                   else (erest, dt')
findErasedFrom defs pos tm = pure ([], [])

-- Find the argument positions in the given type which are guaranteed to be
-- erasable
export
findErased : {auto c : Ref Ctxt Defs} ->
             ClosedTerm -> Core (List Nat, List Nat)
findErased tm
    = do defs <- get Ctxt
         tmnf <- nf defs [] tm
         findErasedFrom defs 0 tmnf

export
updateErasable : {auto c : Ref Ctxt Defs} ->
                 Name -> Core ()
updateErasable n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         (es, dtes) <- findErased (type gdef)
         addDef n (record { eraseArgs = es,
                            safeErase = dtes } gdef)
         pure ()
