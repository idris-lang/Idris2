module TTImp.Elab.Utils

import Core.Case.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

import Data.SnocList

%default covering

detagSafe : {auto c : Ref Ctxt Defs} ->
            Defs -> NF [<] -> Core Bool
detagSafe defs (NTCon _ n _ _ args)
    = do Just (TCon _ _ _ _ _ _ _ (Just detags)) <- lookupDefExact n (gamma defs)
              | _ => pure False
         args' <- traverse (evalClosure defs . snd) (toList args)
         pure $ notErased 0 detags args'
  where
    -- if any argument positions are in the detaggable set, and unerased, then
    -- detagging is safe
    notErased : Nat -> List Nat -> List (NF [<]) -> Bool
    notErased i [] _ = True -- Don't need an index available
    notErased i ns [] = False
    notErased i ns (NErased _ Impossible :: rest)
        = notErased (i + 1) ns rest -- Can't detag here, look elsewhere
    notErased i ns (_ :: rest) -- Safe to detag via this argument
        = elem i ns || notErased (i + 1) ns rest
detagSafe defs _ = pure False

findErasedFrom : {auto c : Ref Ctxt Defs} ->
                 Defs -> Nat -> NF [<] -> Core (List Nat, List Nat)
findErasedFrom defs pos (NBind fc x (Pi _ c _ aty) scf)
    = do -- In the scope, use 'Erased fc Impossible' to mean 'argument is erased'.
         -- It's handy here, because we can use it to tell if a detaggable
         -- argument position is available
         sc <- scf defs (toClosure defaultOpts [<] (Erased fc (ifThenElse (isErased c) Impossible Placeholder)))
         (erest, dtrest) <- findErasedFrom defs (1 + pos) sc
         let dt' = if !(detagSafe defs !(evalClosure defs aty))
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
         tmnf <- nf defs [<] tm
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
bindNotReq fc i (env :< b) Refl ns tm
   = let tmptm = subst (Ref fc Bound (MN "arg" i)) tm
         (ns', btm) = bindNotReq fc (1 + i) env Refl ns tmptm in
         (ns', refToLocal (MN "arg" i) _ btm)
bindNotReq fc i (env :< b) (Keep p) ns tm
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
    notLets : List Name -> (vars : SnocList Name) -> Env Term vars -> List Name
    notLets acc [<] _ = acc
    notLets acc (vs :< v) (env :< b) = if isLet b then notLets acc vs env
                                       else notLets (v :: acc) vs env
bindReq {vs = _ :< n} fc (env :< b) (Keep p) ns tm
    = do b' <- shrinkBinder b p
         bindReq fc env p ((plicit b, n) :: ns)
            (Bind fc _ (Pi (binderLoc b) (multiplicity b) Explicit (binderType b')) tm)
bindReq fc (env :< b) (Drop p) ns tm
    = bindReq fc env p ns tm

-- This machinery is to calculate whether any top level argument is used
-- more than once in a case block, in which case inlining wouldn't be safe
-- since it might duplicate work.

data ArgUsed = Used1 -- been used
             | Used0 -- not used
             | LocalVar -- don't care if it's used

data Usage : SnocList Name -> Type where
     Nil : Usage [<]
     (::) : ArgUsed -> Usage xs -> Usage (xs :< x)

initUsed : (xs : SnocList Name) -> Usage xs
initUsed [<] = []
initUsed (xs :< x) = Used0 :: initUsed xs

initUsedCase : (xs : SnocList Name) -> Usage xs
initUsedCase [<] = []
initUsedCase [<x] = [Used0]
initUsedCase (xs :< x) = LocalVar :: initUsedCase xs

setUsedVar : {idx : _} ->
             (0 _ : IsVar n idx xs) -> Usage xs -> Usage xs
setUsedVar First (Used0 :: us) = Used1 :: us
setUsedVar (Later p) (x :: us) = x :: setUsedVar p us
setUsedVar First us = us

isUsed : {idx : _} ->
         (0 _ : IsVar n idx xs) -> Usage xs -> Bool
isUsed First (Used1 :: us) = True
isUsed First (_ :: us) = False
isUsed (Later p) (_ :: us) = isUsed p us

data Used : Type where

setUsed : {idx : _} ->
          {auto u : Ref Used (Usage vars)} ->
          (0 _ : IsVar n idx vars) -> Core ()
setUsed p = update Used $ setUsedVar p

extendUsed : ArgUsed -> (new : SnocList Name) -> Usage vars -> Usage (vars ++ new)
extendUsed a [<] x = x
extendUsed a (xs :< y) x = a :: extendUsed a xs x

dropUsed : (new : SnocList Name) -> Usage (vars ++ new) -> Usage vars
dropUsed [<] x = x
dropUsed (xs :< x) (u :: us) = dropUsed xs us

inExtended : ArgUsed -> (new : SnocList Name) ->
             {auto u : Ref Used (Usage vars)} ->
             (Ref Used (Usage (vars ++ new)) -> Core a) ->
             Core a
inExtended a new sc
    = do used <- get Used
         u' <- newRef Used (extendUsed a new used)
         res <- sc u'
         put Used (dropUsed new !(get Used @{u'}))
         pure res

termInlineSafe : {vars : _} ->
                 {auto u : Ref Used (Usage vars)} ->
                 Term vars -> Core Bool
termInlineSafe (Local fc isLet idx p)
   = if isUsed p !(get Used)
        then pure False
         else do setUsed p
                 pure True
termInlineSafe (Meta fc x y xs)
    = allInlineSafe xs
  where
    allInlineSafe : List (Term vars) -> Core Bool
    allInlineSafe [] = pure True
    allInlineSafe (x :: xs)
        = do xok <- termInlineSafe x
             if xok
                then allInlineSafe xs
                else pure False
termInlineSafe (Bind fc x b scope)
   = do bok <- binderInlineSafe b
        if bok
           then inExtended LocalVar [<x] (\u' => termInlineSafe scope)
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

mutual
  caseInlineSafe : {vars : _} ->
                   {auto u : Ref Used (Usage vars)} ->
                   CaseTree vars -> Core Bool
  caseInlineSafe (Case idx p scTy xs)
      = if isUsed p !(get Used)
           then pure False
           else do setUsed p
                   altsSafe xs
    where
      altsSafe : List (CaseAlt vars) -> Core Bool
      altsSafe [] = pure True
      altsSafe (a :: as)
          = do u <- get Used
               aok <- caseAltInlineSafe a
               if aok
                  then do -- We can reset the usage information, because we're
                          -- only going to use one alternative at a time
                          put Used u
                          altsSafe as
                  else pure False
  caseInlineSafe (STerm x tm) = termInlineSafe tm
  caseInlineSafe (Unmatched msg) = pure True
  caseInlineSafe Impossible = pure True

  caseAltInlineSafe : {vars : _} ->
                      {auto u : Ref Used (Usage vars)} ->
                      CaseAlt vars -> Core Bool
  caseAltInlineSafe (ConCase x tag args sc)
      = inExtended Used0 args (\u' => caseInlineSafe sc)
  caseAltInlineSafe (DelayCase ty arg sc)
      = inExtended Used0 [<ty, arg] (\u' => caseInlineSafe sc)
  caseAltInlineSafe (ConstCase x sc) = caseInlineSafe sc
  caseAltInlineSafe (DefaultCase sc) = caseInlineSafe sc

-- An inlining is safe if no variable is used more than once in the tree,
-- which means that there's no risk of an input being evaluated more than
-- once after the definition is expanded.
export
inlineSafe : {vars : _} ->
             CaseTree vars -> Core Bool
inlineSafe t
    = do u <- newRef Used (initUsed vars)
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
         u <- newRef Used (initUsedCase vars)
         caseInlineSafe rtree
