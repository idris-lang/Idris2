module Core.Termination

import Core.CaseTree
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import Control.Monad.State

import Libraries.Data.NameMap
import Data.List

%default covering

-- Check that the names a function refers to are terminating
totRefs : {auto c : Ref Ctxt Defs} ->
          Defs -> List Name -> Core Terminating
totRefs defs [] = pure IsTerminating
totRefs defs (n :: ns)
    = do rest <- totRefs defs ns
         Just d <- lookupCtxtExact n (gamma defs)
              | Nothing => pure rest
         case isTerminating (totality d) of
              IsTerminating => pure rest
              Unchecked => do
                log "totality" 20 $ "Totality unchecked for " ++ show !(toFullNames n)
                pure rest
              _ => case rest of
                          NotTerminating (BadCall ns)
                             => toFullNames $ NotTerminating (BadCall (n :: ns))
                          _ => toFullNames $ NotTerminating (BadCall [n])

totRefsIn : {auto c : Ref Ctxt Defs} ->
            Defs -> Term vars -> Core Terminating
totRefsIn defs ty = totRefs defs (keys (getRefs (Resolved (-1)) ty))

-- Check if all branches end up as constructor arguments, with no other
-- function application, and set 'AllGuarded' if so.
-- This is to check whether a function can be considered a constructor form
-- for the sake of termination checking (and might have other uses...)
export
checkIfGuarded : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Core ()
checkIfGuarded fc n
    = do log "totality.termination.guarded" 6 $ "Check if Guarded: " ++ show !(toFullNames n)
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

-- Equal for the purposes of size change means, ignoring as patterns, all
-- non-metavariable positions are equal
scEq : Term vars -> Term vars -> Bool
scEq (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
scEq (Ref _ _ n) (Ref _ _ n') = n == n'
scEq (Meta _ _ i args) _ = True
scEq _ (Meta _ _ i args) = True
scEq (Bind _ _ b sc) (Bind _ _ b' sc') = False -- not checkable
scEq (App _ f a) (App _ f' a') = scEq f f' && scEq a a'
scEq (As _ _ a p) p' = scEq p p'
scEq p (As _ _ a p') = scEq p p'
scEq (TDelayed _ _ t) (TDelayed _ _ t') = scEq t t'
scEq (TDelay _ _ t x) (TDelay _ _ t' x') = scEq t t' && scEq x x'
scEq (TForce _ _ t) (TForce _ _ t') = scEq t t'
scEq (PrimVal _ c) (PrimVal _ c') = c == c'
scEq (Erased _ _) (Erased _ _) = True
scEq (TType _) (TType _) = True
scEq _ _ = False

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

-- Remove all force and delay annotations which are nothing to do with
-- coinduction meaning that all Delays left guard coinductive calls.
delazy : Defs -> Term vars -> Term vars
delazy defs (TDelayed fc r tm)
    = let tm' = delazy defs tm in
          case r of
               LInf => TDelayed fc r tm'
               _ => tm'
delazy defs (TDelay fc r ty tm)
    = let ty' = delazy defs ty
          tm' = delazy defs tm in
          case r of
               LInf => TDelay fc r ty' tm'
               _ => tm'
delazy defs (TForce fc r t)
    = case r of
           LInf => TForce fc r (delazy defs t)
           _ => delazy defs t
delazy defs (Meta fc n i args) = Meta fc n i (map (delazy defs) args)
delazy defs (Bind fc x b sc)
    = Bind fc x (map (delazy defs) b) (delazy defs sc)
delazy defs (App fc f a) = App fc (delazy defs f) (delazy defs a)
delazy defs (As fc s a p) = As fc s (delazy defs a) (delazy defs p)
delazy defs tm = tm

mutual
  findSC : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Defs -> Env Term vars -> Guardedness ->
           List (Nat, Term vars) -> -- LHS args and their position
           Term vars -> -- Right hand side
           Core (List SCCall)
  findSC {vars} defs env g pats (Bind fc n b sc)
       = pure $
            !(findSCbinder b) ++
            !(findSC defs (b :: env) g (map (\ (p, tm) => (p, weaken tm)) pats) sc)
    where
      findSCbinder : Binder (Term vars) -> Core (List SCCall)
      findSCbinder (Let _ c val ty) = findSC defs env g pats val
      findSCbinder b = pure [] -- only types, no need to look
  -- If we're Guarded and find a Delay, continue with the argument as InDelay
  findSC defs env Guarded pats (TDelay _ _ _ tm)
      = findSC defs env InDelay pats tm
  findSC defs env g pats (TDelay _ _ _ tm)
      = findSC defs env g pats tm
  findSC defs env g pats tm
      = do let (fn, args) = getFnArgs tm
           -- if it's a 'case' or 'if' just go straight into the arguments
           Nothing <- handleCase fn args
               | Just res => pure res
           fn' <- conIfGuarded fn -- pretend it's a data constructor if
                                  -- it has the AllGuarded flag
           case (g, fn', args) of
    -- If we're InDelay and find a constructor (or a function call which is
    -- guaranteed to return a constructor; AllGuarded set), continue as InDelay
             (InDelay, Ref fc (DataCon _ _) cn, args) =>
                 do scs <- traverse (findSC defs env InDelay pats) args
                    pure (concat scs)
             -- If we're InDelay otherwise, just check the arguments, the
             -- function call is okay
             (InDelay, _, args) =>
                 do scs <- traverse (findSC defs env Unguarded pats) args
                    pure (concat scs)
             (Guarded, Ref fc (DataCon _ _) cn, args) =>
                 do scs <- traverse (findSC defs env Guarded pats) args
                    pure (concat scs)
             (Toplevel, Ref fc (DataCon _ _) cn, args) =>
                 do scs <- traverse (findSC defs env Guarded pats) args
                    pure (concat scs)
             (_, Ref fc Func fn, args) =>
                 do Just ty <- lookupTyExact fn (gamma defs)
                         | Nothing =>
                              findSCcall defs env Unguarded pats fc fn 0 args
                    arity <- getArity defs [] ty
                    findSCcall defs env Unguarded pats fc fn arity args
             (_, f, args) =>
                 do scs <- traverse (findSC defs env Unguarded pats) args
                    pure (concat scs)
      where
        handleCase : Term vars -> List (Term vars) -> Core (Maybe (List SCCall))
        handleCase (Ref fc nt n) args
            = do n' <- toFullNames n
                 if caseFn n'
                    then Just <$> findSCcall defs env g pats fc n 4 args
                    else pure Nothing
        handleCase _ _ = pure Nothing

        conIfGuarded : Term vars -> Core (Term vars)
        conIfGuarded (Ref fc Func n)
            = do defs <- get Ctxt
                 Just gdef <- lookupCtxtExact n (gamma defs)
                      | Nothing => pure $ Ref fc Func n
                 if AllGuarded `elem` flags gdef
                    then pure $ Ref fc (DataCon 0 0) n
                    else pure $ Ref fc Func n
        conIfGuarded tm = pure tm

  -- Expand the size change argument list with 'Nothing' to match the given
  -- arity (i.e. the arity of the function we're calling) to ensure that
  -- it's noted that we don't know the size change relationship with the
  -- extra arguments.
  expandToArity : Nat -> List (Maybe (Nat, SizeChange)) ->
                  List (Maybe (Nat, SizeChange))
  expandToArity Z xs = xs
  expandToArity (S k) (x :: xs) = x :: expandToArity k xs
  expandToArity (S k) [] = Nothing :: expandToArity k []

  -- Return whether first argument is structurally smaller than the second.
  smaller : Bool -> -- Have we gone under a constructor yet?
            Defs ->
            Maybe (Term vars) -> -- Asserted bigger thing
            Term vars -> -- Term we're checking
            Term vars -> -- Argument it might be smaller than
            Bool
  smaller inc defs big _ (Erased _ _) = False -- Never smaller than an erased thing!
  -- for an as pattern, it's smaller if it's smaller than either part
  smaller inc defs big s (As _ _ p t)
      = smaller inc defs big s p || smaller inc defs big s t
  smaller True defs big s t
      = s == t || smallerArg True defs big s t
  smaller inc defs big s t = smallerArg inc defs big s t

  assertedSmaller : Maybe (Term vars) -> Term vars -> Bool
  assertedSmaller (Just b) a = scEq b a
  assertedSmaller _ _ = False

  smallerArg : Bool -> Defs ->
               Maybe (Term vars) -> Term vars -> Term vars -> Bool
  smallerArg inc defs big (As _ _ _ s) tm = smallerArg inc defs big s tm
  smallerArg inc defs big s tm
        -- If we hit a pattern that is equal to a thing we've asserted_smaller,
        -- the argument must be smaller
      = assertedSmaller big tm ||
                case getFnArgs tm of
                     (Ref _ (DataCon t a) cn, args)
                         => any (smaller True defs big s) args
                     _ => case s of
                               App _ f _ => smaller inc defs big f tm
                                            -- Higher order recursive argument
                               _ => False

  -- if the argument is an 'assert_smaller', return the thing it's smaller than
  asserted : Name -> Term vars -> Maybe (Term vars)
  asserted aSmaller tm
       = case getFnArgs tm of
              (Ref _ nt fn, [_, _, b, _])
                   => if fn == aSmaller
                         then Just b
                         else Nothing
              _ => Nothing

  -- Calculate the size change for the given argument.
  -- i.e., return the size relationship of the given argument with an entry
  -- in 'pats'; the position in 'pats' and the size change.
  -- Nothing if there is no relation with any of them.
  mkChange : Defs -> Name ->
             (pats : List (Nat, Term vars)) ->
             (arg : Term vars) ->
             Maybe (Nat, SizeChange)
  mkChange defs aSmaller [] arg = Nothing
  mkChange defs aSmaller ((i, As _ _ p parg) :: pats) arg
      = mkChange defs aSmaller ((i, p) :: (i, parg) :: pats) arg
  mkChange defs aSmaller ((i, parg) :: pats) arg
      = cond [(scEq arg parg, Just (i, Same)),
              (smaller False defs (asserted aSmaller arg) arg parg, Just (i, Smaller))]
          (mkChange defs aSmaller pats arg)

  -- Given a name of a case function, and a list of the arguments being
  -- passed to it, update the pattern list so that it's referring to the LHS
  -- of the case block function and return the corresponding RHS.
  -- This way, we can build case blocks directly into the size change graph
  -- rather than treating the definitions separately.
  getCasePats : {vars : _} ->
                Defs -> Name -> List (Nat, Term vars) ->
                List (Term vars) ->
                Core (Maybe (List (vs ** (Env Term vs,
                                         List (Nat, Term vs), Term vs))))
  getCasePats {vars} defs n pats args
      = case !(lookupDefExact n (gamma defs)) of
             Just (PMDef _ _ _ _ pdefs)
                => pure $ Just (map matchArgs pdefs)
             _ => pure Nothing
    where
      updateRHS : {vs, vs' : _} ->
                  List (Term vs, Term vs') -> Term vs -> Term vs'
      updateRHS {vs} {vs'} ms tm
          = case lookupTm tm ms of
                 Nothing => urhs tm
                 Just t => t
        where
          urhs : Term vs -> Term vs'
          urhs (Local fc _ _ _) = Erased fc False
          urhs (Ref fc nt n) = Ref fc nt n
          urhs (Meta fc m i margs) = Meta fc m i (map (updateRHS ms) margs)
          urhs (App fc f a) = App fc (updateRHS ms f) (updateRHS ms a)
          urhs (As fc s a p) = As fc s (updateRHS ms a) (updateRHS ms p)
          urhs (TDelayed fc r ty) = TDelayed fc r (updateRHS ms ty)
          urhs (TDelay fc r ty tm)
              = TDelay fc r (updateRHS ms ty) (updateRHS ms tm)
          urhs (TForce fc r tm) = TForce fc r (updateRHS ms tm)
          urhs (Bind fc x b sc)
              = Bind fc x (map (updateRHS ms) b)
                  (updateRHS (map (\vt => (weaken (fst vt), weaken (snd vt))) ms) sc)
          urhs (PrimVal fc c) = PrimVal fc c
          urhs (Erased fc i) = Erased fc i
          urhs (TType fc) = TType fc

          lookupTm : Term vs -> List (Term vs, Term vs') -> Maybe (Term vs')
          lookupTm tm [] = Nothing
          lookupTm (As fc s p tm) tms -- Want to keep the pattern and the variable,
                                      -- if there was an @ in the parent
              = do tm' <- lookupTm tm tms
                   Just $ As fc s tm' (urhs tm)
          lookupTm tm ((As fc s p tm', v) :: tms)
              = if tm == p
                   then Just v
                   else do tm' <- lookupTm tm ((tm', v) :: tms)
                           Just $ As fc s (urhs p) tm'
          lookupTm tm ((tm', v) :: tms)
              = if tm == tm'
                   then Just v
                   else lookupTm tm tms

      updatePat : {vs, vs' : _} ->
                  List (Term vs, Term vs') -> (Nat, Term vs) -> (Nat, Term vs')
      updatePat ms (n, tm) = (n, updateRHS ms tm)

      matchArgs : (vs ** (Env Term vs, Term vs, Term vs)) ->
                  (vs ** (Env Term vs, List (Nat, Term vs), Term vs))
      matchArgs (_ ** (env', lhs, rhs))
         = let patMatch = reverse (zip args (getArgs lhs)) in
               (_ ** (env', map (updatePat patMatch) pats, rhs))

  caseFn : Name -> Bool
  caseFn (CaseBlock _ _) = True
  caseFn (DN _ n) = caseFn n
  caseFn (NS _ n) = caseFn n
  caseFn _ = False

  findSCcall : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Defs -> Env Term vars -> Guardedness ->
               List (Nat, Term vars) ->
               FC -> Name -> Nat -> List (Term vars) ->
               Core (List SCCall)
  findSCcall defs env g pats fc fn_in arity args
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = do Just gdef <- lookupCtxtExact fn_in (gamma defs)
                | Nothing => undefinedName fc fn_in
           let fn = fullname gdef
           log "totality.termination.sizechange" 10 $ "Looking under " ++ show !(toFullNames fn)
           aSmaller <- resolved (gamma defs) (NS builtinNS (UN "assert_smaller"))
           cond [(fn == NS builtinNS (UN "assert_total"), pure []),
              (caseFn fn,
                  do mps <- getCasePats defs fn pats args
                     case mps of
                          Nothing => pure Prelude.Nil
                          Just ps => do scs <- traverse (findInCase defs g) ps
                                        pure (concat scs))]
              (do scs <- traverse (findSC defs env g pats) args
                  pure ([MkSCCall fn
                           (expandToArity arity
                                (map (mkChange defs aSmaller pats) args))]
                           ++ concat scs))

  findInCase : {auto c : Ref Ctxt Defs} ->
               Defs -> Guardedness ->
               (vs ** (Env Term vs, List (Nat, Term vs), Term vs)) ->
               Core (List SCCall)
  findInCase defs g (_ ** (env, pats, tm))
     = do logC "totality" 10 $
                   do ps <- traverse toFullNames (map snd pats)
                      pure ("Looking in case args " ++ show ps)
          logTermNF "totality" 10 "        =" env tm
          rhs <- normaliseOpts tcOnly defs env tm
          findSC defs env g pats (delazy defs rhs)

findCalls : {auto c : Ref Ctxt Defs} ->
            Defs -> (vars ** (Env Term vars, Term vars, Term vars)) ->
            Core (List SCCall)
findCalls defs (_ ** (env, lhs, rhs_in))
   = do let pargs = getArgs (delazy defs lhs)
        rhs <- normaliseOpts tcOnly defs env rhs_in
        findSC defs env Toplevel
               (zip (take (length pargs) [0..]) pargs) (delazy defs rhs)

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (PMDef _ args _ _ pats)
   = do sc <- traverse (findCalls defs) pats
        pure $ nub (concat sc)
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do log "totality.termination.sizechange" 5 $ "Calculating Size Change: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         getSC defs (definition def)

Arg : Type
Arg = Int

data APos : Type where

firstArg : Arg
firstArg = 0

nextArg : Arg -> Arg
nextArg x = x + 1

initArgs : {auto a : Ref APos Arg} ->
           Nat -> Core (List (Maybe (Arg, SizeChange)))
initArgs Z = pure []
initArgs (S k)
    = do arg <- get APos
         put APos (nextArg arg)
         args' <- initArgs k
         pure (Just (arg, Same) :: args')

-- Traverse the size change graph. When we reach a point we've seen before,
-- at least one of the arguments must have got smaller, otherwise it's
-- potentially non-terminating
checkSC : {auto a : Ref APos Arg} ->
          {auto c : Ref Ctxt Defs} ->
          Defs ->
          Name -> -- function we're checking
          List (Maybe (Arg, SizeChange)) -> -- functions arguments and change
          List (Name, List (Maybe Arg)) -> -- calls we've seen so far
          Core Terminating
checkSC defs f args path
   = do log "totality.termination.sizechange" 7 $ "Checking Size Change Graph: " ++ show !(toFullNames f)
        let pos = (f, map (map Builtin.fst) args)
        if pos `elem` path
           then do log "totality.termination.sizechange.inPath" 8 $ "Checking arguments: " ++ show !(toFullNames f)
                   toFullNames $ checkDesc (mapMaybe (map Builtin.snd) args) path
           else case !(lookupCtxtExact f (gamma defs)) of
                     Nothing => do log "totality.termination.sizechange.isTerminating" 8 $ "Size Change Graph is Terminating for: " ++ show !(toFullNames f)
                                   pure IsTerminating
                     Just def => do log "totality.termination.sizechange.needsChecking" 8 $ "Size Change Graph needs traversing: " ++ show !(toFullNames f)
                                    continue (sizeChange def) (pos :: path)
  where
    -- Look for something descending in the list of size changes
    checkDesc : List SizeChange -> List (Name, List (Maybe Arg)) -> Terminating
    checkDesc [] path = NotTerminating (RecPath (reverse (map fst path)))
    checkDesc (Smaller :: _) _ = IsTerminating
    checkDesc (_ :: xs) path = checkDesc xs path

    getPos : forall a . List a -> Nat -> Maybe a
    getPos [] _ = Nothing
    getPos (x :: xs) Z = Just x
    getPos (x :: xs) (S k) = getPos xs k

    updateArg : SizeChange -> Maybe (Arg, SizeChange) -> Maybe (Arg, SizeChange)
    updateArg c Nothing = Nothing
    updateArg c arg@(Just (i, Unknown)) = arg
    updateArg Unknown (Just (i, _)) = Just (i, Unknown)
    updateArg c (Just (i, Same)) = Just (i, c)
    updateArg c arg = arg

    mkArgs : List (Maybe (Nat, SizeChange)) -> List (Maybe (Arg, SizeChange))
    mkArgs [] = []
    mkArgs (Nothing :: xs) = Nothing :: mkArgs xs
    mkArgs (Just (pos, c) :: xs)
        = case getPos args pos of
               Nothing => Nothing :: mkArgs xs
               Just arg => updateArg c arg :: mkArgs xs

    checkCall : List (Name, List (Maybe Arg)) -> SCCall -> Core Terminating
    checkCall path sc
        = do let inpath = fnCall sc `elem` map fst path
             Just gdef <- lookupCtxtExact (fnCall sc) (gamma defs)
                  | Nothing => pure IsTerminating -- nothing to check
             let Unchecked = isTerminating (totality gdef)
                  | IsTerminating => pure IsTerminating
                  | _ => pure (NotTerminating (BadCall [fnCall sc]))
             log "totality.termination.sizechange.checkCall" 8 $ "CheckCall Size Change Graph: " ++ show !(toFullNames (fnCall sc))
             term <- checkSC defs (fnCall sc) (mkArgs (fnArgs sc)) path
             if not inpath
                then case term of
                       NotTerminating (RecPath _) =>
                          -- might have lost information while assuming this
                          -- was mutually recursive, so start again with new
                          -- arguments (that is, where we'd start if the
                          -- function was the top level thing we were checking)
                          do log "totality.termination.sizechange.checkCall.inPathNot.restart" 9 $ "ReChecking Size Change Graph: " ++ show !(toFullNames (fnCall sc))
                             args' <- initArgs (length (fnArgs sc))
                             checkSC defs (fnCall sc) args' path
                       t => do log "totality.termination.sizechange.checkCall.inPathNot.return" 9 $ "Have result: " ++ show !(toFullNames (fnCall sc))
                               pure t
                else do log "totality.termination.sizechange.checkCall.inPath" 9 $ "Have Result: " ++ show !(toFullNames (fnCall sc))
                        pure term

    getWorst : Terminating -> List Terminating -> Terminating
    getWorst term [] = term
    getWorst term (IsTerminating :: xs) = getWorst term xs
    getWorst term (Unchecked :: xs) = getWorst Unchecked xs
    getWorst term (bad :: xs) = bad

    continue : List SCCall -> List (Name, List (Maybe Arg)) -> Core Terminating
    continue scs path
        = do allTerm <- traverse (checkCall path) scs
             pure (getWorst IsTerminating allTerm)

calcTerminating : {auto c : Ref Ctxt Defs} ->
                  FC -> Name -> Core Terminating
calcTerminating loc n
    = do defs <- get Ctxt
         log "totality.termination.calc" 7 $ "Calculating termination: " ++ show !(toFullNames n)
         case !(lookupCtxtExact n (gamma defs)) of
              Nothing => undefinedName loc n
              Just def =>
                case !(totRefs defs (nub !(addCases defs (keys (refersTo def))))) of
                     IsTerminating =>
                        do let ty = type def
                           a <- newRef APos firstArg
                           args <- initArgs !(getArity defs [] ty)
                           checkSC defs n args []
                     bad => pure bad
  where
    addCases' : Defs -> NameMap () -> List Name -> Core (List Name)
    addCases' defs all [] = pure (keys all)
    addCases' defs all (n :: ns)
        = case lookup n all of
             Just _ => addCases' defs all ns
             Nothing =>
               if caseFn !(getFullName n)
                  then case !(lookupCtxtExact n (gamma defs)) of
                            Just def => addCases' defs (insert n () all)
                                                  (keys (refersTo def) ++ ns)
                            Nothing => addCases' defs (insert n () all) ns
                  else addCases' defs (insert n () all) ns

    addCases : Defs -> List Name -> Core (List Name)
    addCases defs ns = addCases' defs empty ns

-- Check whether a function is terminating, and record in the context
export
checkTerminating : {auto c : Ref Ctxt Defs} ->
                   FC -> Name -> Core Terminating
checkTerminating loc n
    = do tot <- getTotality loc n
         log "totality.termination" 6 $ "Checking termination: " ++ show !(toFullNames n)
         case isTerminating tot of
              Unchecked =>
                 do tot' <- calcTerminating loc n
                    setTerminating loc n tot'
                    pure tot'
              t => pure t

nameIn : {auto c : Ref Ctxt Defs} ->
         Defs -> List Name -> NF [] -> Core Bool
nameIn defs tyns (NBind fc x b sc)
    = if !(nameIn defs tyns (binderType b))
         then pure True
         else do sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
                 nameIn defs tyns sc'
nameIn defs tyns (NApp _ _ args)
    = anyM (nameIn defs tyns)
           !(traverse (evalClosure defs . snd) args)
nameIn defs tyns (NTCon _ n _ _ args)
    = if n `elem` tyns
         then pure True
         else do args' <- traverse (evalClosure defs . snd) args
                 anyM (nameIn defs tyns) args'
nameIn defs tyns (NDCon _ n _ _ args)
    = anyM (nameIn defs tyns)
           !(traverse (evalClosure defs . snd) args)
nameIn defs tyns _ = pure False

-- Check an argument type doesn't contain a negative occurrence of any of
-- the given type names
posArg : {auto c : Ref Ctxt Defs} ->
         Defs -> List Name -> NF [] -> Core Terminating
-- a tyn can only appear in the parameter positions of
-- tc; report positivity failure if it appears anywhere else
posArg defs tyns (NTCon _ tc _ _ args)
    = let testargs : List (Closure [])
             = case !(lookupDefExact tc (gamma defs)) of
                    Just (TCon _ _ params _ _ _ _ _) =>
                         dropParams 0 params (map snd args)
                    _ => map snd args
      in if !(anyM (nameIn defs tyns)
                  !(traverse (evalClosure defs) testargs))
             then pure (NotTerminating NotStrictlyPositive)
             else pure IsTerminating
  where
    dropParams : Nat -> List Nat -> List (Closure []) -> List (Closure [])
    dropParams i ps [] = []
    dropParams i ps (x :: xs)
        = if i `elem` ps
             then dropParams (S i) ps xs
             else x :: dropParams (S i) ps xs
-- a tyn can not appear as part of ty
posArg defs tyns (NBind fc x (Pi _ _ e ty) sc)
    = if !(nameIn defs tyns ty)
         then pure (NotTerminating NotStrictlyPositive)
         else do sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
                 posArg defs tyns sc'
posArg defs tyn _ = pure IsTerminating

checkPosArgs : {auto c : Ref Ctxt Defs} ->
               Defs -> List Name -> NF [] -> Core Terminating
checkPosArgs defs tyns (NBind fc x (Pi _ _ e ty) sc)
    = case !(posArg defs tyns ty) of
           IsTerminating =>
                checkPosArgs defs tyns
                       !(sc defs (toClosure defaultOpts [] (Erased fc False)))
           bad => pure bad
checkPosArgs defs tyns _ = pure IsTerminating

checkCon : {auto c : Ref Ctxt Defs} ->
           Defs -> List Name -> Name -> Core Terminating
checkCon defs tyns cn
    = case !(lookupTyExact cn (gamma defs)) of
           Nothing => pure Unchecked
           Just ty =>
                case !(totRefsIn defs ty) of
                     IsTerminating => checkPosArgs defs tyns !(nf defs [] ty)
                     bad => pure bad

checkData : {auto c : Ref Ctxt Defs} ->
            Defs -> List Name -> List Name -> Core Terminating
checkData defs tyns [] = pure IsTerminating
checkData defs tyns (c :: cs)
    = case !(checkCon defs tyns c) of
           IsTerminating => checkData defs tyns cs
           bad => pure bad

-- Calculate whether a type satisfies the strict positivity condition, and
-- return whether it's terminating, along with its data constructors
calcPositive : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Core (Terminating, List Name)
calcPositive loc n
    = do defs <- get Ctxt
         log "totality.positivity" 6 $ "Calculating positivity: " ++ show !(toFullNames n)
         case !(lookupDefTyExact n (gamma defs)) of
              Just (TCon _ _ _ _ _ tns dcons _, ty) =>
                  case !(totRefsIn defs ty) of
                       IsTerminating =>
                            do t <- checkData defs (n :: tns) dcons
                               pure (t , dcons)
                       bad => pure (bad, dcons)
              Just _ => throw (GenericMsg loc (show n ++ " not a data type"))
              Nothing => undefinedName loc n

-- Check whether a data type satisfies the strict positivity condition, and
-- record in the context
export
checkPositive : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Terminating
checkPositive loc n_in
    = do n <- toResolvedNames n_in
         tot <- getTotality loc n
         log "totality.positivity" 6 $ "Checking positivity: " ++ show !(toFullNames n)
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
         log "totality" 5 $ "Checking totality: " ++ show !(toFullNames n)
         defs <- get Ctxt
         case isTerminating tot of
              Unchecked =>
                  case !(lookupDefExact n (gamma defs)) of
                       Just (TCon _ _ _ _ _ _ _ _)
                           => checkPositive loc n
                       _ => checkTerminating loc n
              t => pure t
