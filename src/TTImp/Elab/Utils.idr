module TTImp.Elab.Utils

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

%default covering

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
    notErased i ns (_ :: rest) -- Safe to detag via this argument
        = elem i ns || notErased (i + 1) ns rest
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
export
wrapErrorC : List ElabOpt -> (Error -> Error) -> Core a -> Core a
wrapErrorC opts err
    = if InCase `elem` opts
         then id
         else wrapError err

plicit : Binder (Term vars) -> PiInfo RawImp
plicit (Pi _ p _) = forgetDef p
plicit (PVar _ p _) = forgetDef p
plicit _ = Explicit

export
bindNotReq : {vs : _} ->
             FC -> Int -> Env Term vs -> (sub : SubVars pre vs) ->
             List (PiInfo RawImp, Name) ->
             Term vs -> (List (PiInfo RawImp, Name), Term pre)
bindNotReq fc i [] SubRefl ns tm = (ns, embed tm)
bindNotReq fc i (b :: env) SubRefl ns tm
   = let tmptm = subst (Ref fc Bound (MN "arg" i)) tm
         (ns', btm) = bindNotReq fc (1 + i) env SubRefl ns tmptm in
         (ns', refToLocal (MN "arg" i) _ btm)
bindNotReq fc i (b :: env) (KeepCons p) ns tm
   = let tmptm = subst (Ref fc Bound (MN "arg" i)) tm
         (ns', btm) = bindNotReq fc (1 + i) env p ns tmptm in
         (ns', refToLocal (MN "arg" i) _ btm)
bindNotReq {vs = n :: _} fc i (b :: env) (DropCons p) ns tm
   = bindNotReq fc i env p ((plicit b, n) :: ns)
       (Bind fc _ (Pi (multiplicity b) Explicit (binderType b)) tm)

export
bindReq : {vs : _} ->
          FC -> Env Term vs -> (sub : SubVars pre vs) ->
          List (PiInfo RawImp, Name) ->
          Term pre -> Maybe (List (PiInfo RawImp, Name), List Name, ClosedTerm)
bindReq {vs} fc env SubRefl ns tm
    = pure (ns, notLets [] _ env, abstractEnvType fc env tm)
  where
    notLets : List Name -> (vars : List Name) -> Env Term vars -> List Name
    notLets acc [] _ = acc
    notLets acc (v :: vs) (Let _ _ _ :: env) = notLets acc vs env
    notLets acc (v :: vs) (_ :: env) = notLets (v :: acc) vs env
bindReq {vs = n :: _} fc (b :: env) (KeepCons p) ns tm
    = do b' <- shrinkBinder b p
         bindReq fc env p ((plicit b, n) :: ns)
            (Bind fc _ (Pi (multiplicity b) Explicit (binderType b')) tm)
bindReq fc (b :: env) (DropCons p) ns tm
    = bindReq fc env p ns tm
