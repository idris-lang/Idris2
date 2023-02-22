module Core.Termination.CallGraph

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Value

import Data.String

%default covering

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

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
scEq (TType _ _) (TType _ _) = True
scEq _ _ = False

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
                 do logC "totality" 50 $
                       pure $ "Looking up type of " ++ show !(toFullNames fn)
                    Just ty <- lookupTyExact fn (gamma defs)
                         | Nothing => do
                              log "totality" 50 $ "Lookup failed"
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
  getCasePats : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Defs -> Name -> List (Nat, Term vars) ->
                List (Term vars) ->
                Core (Maybe (List (vs ** (Env Term vs,
                                         List (Nat, Term vs), Term vs))))
  getCasePats {vars} defs n pats args
      = do Just (PMDef _ _ _ _ pdefs) <- lookupDefExact n (gamma defs)
             | _ => pure Nothing
           log "totality" 20 $
             unwords ["Looking at the", show (length pdefs), "cases of", show  n]
           let pdefs' = map matchArgs pdefs
           logC "totality" 20 $ do
              old <- for pdefs $ \ (_ ** (_, lhs, rhs)) => do
                       lhs <- toFullNames lhs
                       rhs <- toFullNames rhs
                       pure $ "    " ++ show lhs ++ " => " ++ show rhs
              new <- for pdefs' $ \ (_ ** (_, lhs, rhs)) => do
                       lhs <- traverse (toFullNames . snd) lhs
                       rhs <- toFullNames rhs
                       pure $ "    " ++ show lhs ++ " => " ++ show rhs
              pure $ unlines $ "Updated" :: old ++ "  to:" :: new
           pure $ Just pdefs'

    where
      updateRHS : {vs, vs' : _} ->
                  List (Term vs, Term vs') -> Term vs -> Term vs'
      updateRHS {vs} {vs'} ms tm
          = case lookupTm tm ms of
                 Nothing => urhs tm
                 Just t => t
        where
          urhs : Term vs -> Term vs'
          urhs (Local fc _ _ _) = Erased fc Placeholder
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
          urhs (Erased fc Impossible) = Erased fc Impossible
          urhs (Erased fc Placeholder) = Erased fc Placeholder
          urhs (Erased fc (Dotted t)) = Erased fc (Dotted (updateRHS ms t))
          urhs (TType fc u) = TType fc u

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

  findSCcall : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Defs -> Env Term vars -> Guardedness ->
               List (Nat, Term vars) ->
               FC -> Name -> Nat -> List (Term vars) ->
               Core (List SCCall)
  findSCcall defs env g pats fc fn_in arity args
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = do fn <- getFullName fn_in
           log "totality.termination.sizechange" 10 $ "Looking under " ++ show !(toFullNames fn)
           aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
           cond [(fn == NS builtinNS (UN $ Basic "assert_total"), pure [])
                ,(caseFn fn,
                    do scs1 <- traverse (findSC defs env g pats) args
                       mps  <- getCasePats defs fn pats args
                       scs2 <- traverse (findInCase defs g) $ fromMaybe [] mps
                       pure (concat (scs1 ++ scs2)))
              ]
              (do scs <- traverse (findSC defs env g pats) args
                  pure ([MkSCCall fn
                           (expandToArity arity
                                (map (mkChange defs aSmaller pats) args))
                           fc]
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
