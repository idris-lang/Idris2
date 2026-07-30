module TTImp.Elab.Utils

import Core.Case.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

import Data.SnocList
import Data.SnocList.Quantifiers

import Libraries.Data.NatSet
import Libraries.Data.VarSet
import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.Quantifiers.Extra as Lib

%default covering

detagSafe : {auto c : Ref Ctxt Defs} ->
            Defs -> ClosedNF -> Core Bool
detagSafe defs (NTCon _ n _ args)
    = do Just (TCon _ _ _ _ _ _ (Just detags)) <- lookupDefExact n (gamma defs)
              | _ => pure False
         args' <- traverse (evalClosure defs . snd) args
         pure $ NatSet.isEmpty detags || notErased 0 detags (toList args')
  where
    -- if any argument positions are in the non-empty(!) detaggable set, and unerased, then
    -- detagging is safe
    notErased : Nat -> NatSet -> List ClosedNF -> Bool
    notErased i ns [] = False
    notErased i ns (NErased _ Impossible :: rest)
        = notErased (i + 1) ns rest -- Can't detag here, look elsewhere
    notErased i ns (_ :: rest) -- Safe to detag via this argument
        = elem i ns || notErased (i + 1) ns rest
detagSafe defs _ = pure False

findErasedFrom : {auto c : Ref Ctxt Defs} ->
                 Defs -> Nat -> ClosedNF -> Core (NatSet, NatSet)
findErasedFrom defs pos (NBind fc x (Pi _ c _ aty) scf)
    = do -- In the scope, use 'Erased fc Impossible' to mean 'argument is erased'.
         -- It's handy here, because we can use it to tell if a detaggable
         -- argument position is available
         sc <- scf defs (toClosure defaultOpts Env.empty (Erased fc (ifThenElse (isErased c) Impossible Placeholder)))
         (erest, dtrest) <- findErasedFrom defs (1 + pos) sc
         let dt' = if !(detagSafe defs !(evalClosure defs aty))
                      then (insert pos dtrest) else dtrest
         pure $ if isErased c
                   then (insert pos erest, dt')
                   else (erest, dt')
findErasedFrom defs pos tm = pure (NatSet.empty, NatSet.empty)

-- Find the argument positions in the given type which are guaranteed to be
-- erasable
export
findErased : {auto c : Ref Ctxt Defs} ->
             ClosedTerm -> Core (NatSet, NatSet)
findErased tm
    = do defs <- get Ctxt
         tmnf <- nf defs Env.empty tm
         findErasedFrom defs 0 tmnf

export
updateErasable : {auto c : Ref Ctxt Defs} ->
                 Name -> Core ()
updateErasable n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         (es, dtes) <- findErased (type gdef)
         ignore $ addDef n $
                    { eraseArgs := es,
                      safeErase := dtes } gdef

export
wrapErrorC : List ElabOpt -> (Error -> Error) -> Core a -> Core a
wrapErrorC opts err
    = if InCase `elem` opts
         then id
         else wrapError err

plicit : Binder (Term vars) -> PiInfo RawImp
plicit (Pi _ _ p _) = forgetDef p
plicit (PVar _ _ p _) = forgetDef p
plicit _ = Explicit

export
bindNotReq : {vs : _} ->
             FC -> Int -> Env Term vs -> (sub : Thin pre vs) ->
             List (PiInfo RawImp, Name) ->
             Term vs -> (List (PiInfo RawImp, Name), Term pre)
bindNotReq fc i [<] Refl ns tm = (ns, embed tm)
bindNotReq {vs = _ :< _} fc i (env :< b) Refl ns tm
   = let tmptm = subst (Ref fc Bound (MN "arg" i)) tm
         (ns', btm) = bindNotReq fc (1 + i) env Refl ns tmptm in
         (ns', refToLocal (MN "arg" i) _ btm)
bindNotReq {vs = _ :< _} fc i (env :< b) (Keep p) ns tm
   = let tmptm = subst (Ref fc Bound (MN "arg" i)) tm
         (ns', btm) = bindNotReq fc (1 + i) env p ns tmptm in
         (ns', refToLocal (MN "arg" i) _ btm)
bindNotReq {vs = _ :< n} fc i (env :< b) (Drop p) ns tm
   = bindNotReq fc i env p ((plicit b, n) :: ns)
       (Bind fc _ (Pi (binderLoc b) (multiplicity b) Explicit (binderType b)) tm)

export
bindReq : {vs : _} ->
          FC -> Env Term vs -> (sub : Thin pre vs) ->
          List (PiInfo RawImp, Name) ->
          Term pre -> Maybe (List (PiInfo RawImp, Name), List Name, ClosedTerm)
bindReq {vs} fc env Refl ns tm
    = pure (ns, notLets [] _ env, abstractEnvType fc env tm)
  where
    notLets : List Name -> (vars : Scope) -> Env Term vars -> List Name
    notLets acc [<] _ = acc
    notLets acc (vs :< v) (env :< b) = if isLet b then notLets acc vs env
                                       else notLets (v :: acc) vs env
bindReq {vs = _ :< n} fc (env :< b) (Keep p) ns tm
    = do b' <- shrinkBinder b p
         bindReq fc env p ((plicit b, n) :: ns)
            (Bind fc _ (Pi (binderLoc b) (multiplicity b) Explicit (binderType b')) tm)
bindReq {vs = _ :< _} fc (env :< b) (Drop p) ns tm
    = bindReq fc env p ns tm

-- This machinery is to calculate whether any top level argument is used
-- more than once in a case block, in which case inlining wouldn't be safe
-- since it might duplicate work.

data ArgUsed = Used1 -- been used
             | Used0 -- not used
             | LocalVar -- don't care if it's used

record Usage (vs : Scope) where
  constructor MkUsage
  isUsedSet : VarSet vs -- whether it's been used
  isLocalSet : VarSet vs -- don't care if it's used

initUsed : Usage vs
initUsed = MkUsage
  { isUsedSet = VarSet.empty
  , isLocalSet = VarSet.empty
  }

initUsedCase : SizeOf vs -> Usage vs
initUsedCase p = MkUsage
  { isUsedSet = VarSet.empty
  , isLocalSet = case sizedView p of
    Z => VarSet.empty
    S _ => VarSet.delete first (VarSet.full p)
  }

setUsedVar : Var vs -> Usage vs -> Usage vs
setUsedVar v us@(MkUsage isUsedSet isLocalSet)
  = -- if we don't care then we don't change anything
    if v `VarSet.elem` isLocalSet then us
    -- otherwise we record the variable usage
    else MkUsage { isUsedSet = VarSet.insert v isUsedSet
                 , isLocalSet }

isUsed : Var vs -> Usage vs -> Bool
isUsed v us = v `VarSet.elem` isUsedSet us

data Used : Type where

setUsed : {auto u : Ref Used (Usage vars)} ->
          Var vars -> Core ()
setUsed p = update Used $ setUsedVar p

extendUsed : ArgUsed -> SizeOf inner -> Usage vars -> Usage (Scope.ext vars inner)
extendUsed LocalVar p (MkUsage iu il)
  = let p' = cast p in
    rewrite fishAsSnocAppend vars inner in
    MkUsage (weakenNs {tm = VarSet} p' iu) (append p' (full p') il)
extendUsed Used0 p (MkUsage iu il)
  = let p' = cast p in
    rewrite fishAsSnocAppend vars inner in
    MkUsage (weakenNs {tm = VarSet} p' iu) (weakenNs {tm = VarSet} p' il)
extendUsed Used1 p (MkUsage iu il)
  = let p' = cast p in
    rewrite fishAsSnocAppend vars inner in
    MkUsage (append p' (full p') iu) (weakenNs {tm = VarSet} p' il)

dropUsed : SizeOf inner -> Usage (Scope.ext vars inner) -> Usage vars
dropUsed p (MkUsage iu il) = let p' = cast p in
                             MkUsage
                               (VarSet.dropInner {vs = vars} p' (rewrite sym $ fishAsSnocAppend vars inner in iu))
                               (dropInner {vs = vars} p' (rewrite sym $ fishAsSnocAppend vars inner in il))

inExtended : ArgUsed -> SizeOf new ->
             {auto u : Ref Used (Usage vars)} ->
             (Ref Used (Usage (Scope.ext vars new)) -> Core a) ->
             Core a
inExtended a new sc
    = do used <- get Used
         u' <- newRef Used (extendUsed a new used)
         res <- sc u'
         put Used (dropUsed new !(get Used @{u'}))
         pure res

0 InlineSafe : Scoped -> Type
InlineSafe tm
  = {0 vars : Scope} -> {auto u : Ref Used (Usage vars)} ->
    tm vars -> Core Bool

termsInlineSafe : InlineSafe (List . Term)

termInlineSafe : InlineSafe Term
termInlineSafe (Local fc isLet idx p)
   = let v := MkVar p in
     if isUsed v !(get Used)
        then pure False
         else do setUsed v
                 pure True
termInlineSafe (Meta fc x y xs)
    = termsInlineSafe xs
termInlineSafe (Bind fc x b scope)
   = do bok <- binderInlineSafe b
        if bok
           then inExtended LocalVar (suc zero) (\u' => termInlineSafe scope)
           else pure False
  where
    binderInlineSafe : Binder (Term vars) -> Core Bool
    binderInlineSafe (Let _ _ val _) = termInlineSafe val
    binderInlineSafe _ = pure True
termInlineSafe (App fc fn arg)
    = do fok <- termInlineSafe fn
         if fok
            then termInlineSafe arg
            else pure False
termInlineSafe (As fc x as pat) = termInlineSafe pat
termInlineSafe (TDelayed fc x ty) = termInlineSafe ty
termInlineSafe (TDelay fc x ty arg) = termInlineSafe arg
termInlineSafe (TForce fc x val) = termInlineSafe val
termInlineSafe _ = pure True

termsInlineSafe [] = pure True
termsInlineSafe (x :: xs)
    = do xok <- termInlineSafe x
         if xok
            then termsInlineSafe xs
            else pure False

mutual
  caseInlineSafe : InlineSafe CaseTree
  caseInlineSafe (Case idx p scTy xs)
      = let v := MkVar p in
        if isUsed v !(get Used)
           then pure False
           else do setUsed v
                   caseAltsInlineSafe xs
  caseInlineSafe (STerm x tm) = termInlineSafe tm
  caseInlineSafe (Unmatched msg) = pure True
  caseInlineSafe Impossible = pure True

  caseAltsInlineSafe : InlineSafe (List . CaseAlt)
  caseAltsInlineSafe [] = pure True
  caseAltsInlineSafe (a :: as)
      = do u <- get Used
           True <- caseAltInlineSafe a
             | False => pure False
           -- We can reset the usage information, because we're
           -- only going to use one alternative at a time
           put Used u
           caseAltsInlineSafe as

  caseAltInlineSafe : InlineSafe CaseAlt
  caseAltInlineSafe (ConCase x tag args sc)
      -- should these be local vars?
      = inExtended Used0 (mkSizeOf args) (\u' => caseInlineSafe sc)
  caseAltInlineSafe (DelayCase ty arg sc)
      -- should these be local vars?
      = inExtended Used0 (mkSizeOf [ty, arg]) (\u' => caseInlineSafe sc)
  caseAltInlineSafe (ConstCase x sc) = caseInlineSafe sc
  caseAltInlineSafe (DefaultCase sc) = caseInlineSafe sc

-- An inlining is safe if no variable is used more than once in the tree,
-- which means that there's no risk of an input being evaluated more than
-- once after the definition is expanded.
export
inlineSafe : CaseTree vars -> Core Bool
inlineSafe t
    = do u <- newRef Used initUsed
         caseInlineSafe t

export
canInlineDef : {auto c : Ref Ctxt Defs} ->
               Name -> Core Bool
canInlineDef n
    = do defs <- get Ctxt
         Just (PMDef _ _ _ rtree _) <- lookupDefExact n (gamma defs)
             | _ => pure False
         inlineSafe rtree

-- This is a special case because the only argument we actually care about
-- is the last one, since the others are just variables passed through from
-- the environment, and duplicating a variable doesn't cost anything.
export
canInlineCaseBlock : {auto c : Ref Ctxt Defs} ->
                     Name -> Core Bool
canInlineCaseBlock n
    = do defs <- get Ctxt
         Just (PMDef _ vars _ rtree _) <- lookupDefExact n (gamma defs)
             | _ => pure False
         u <- newRef Used (initUsedCase (mkSizeOf vars))
         caseInlineSafe rtree
