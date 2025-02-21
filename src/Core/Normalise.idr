module Core.Normalise

import public Core.Normalise.Convert
import public Core.Normalise.Eval
import public Core.Normalise.Quote

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Options
import Core.TT
import Core.Value

%default covering

-- Expand all the pi bindings at the start of a term, but otherwise don't
-- reduce
export
normalisePis : {auto c : Ref Ctxt Defs} ->
               {vars : List Name} ->
               Defs -> Env Term vars -> Term vars -> Core (Term vars)
normalisePis defs env tm
    = do tmnf <- nf defs env tm
         case tmnf of
              NBind _ _ (Pi _ _ _ _) _ => quoteWithPi defs env tmnf
              _ => pure tm

export
glueBack : {auto c : Ref Ctxt Defs} ->
           {vars : _} ->
           Defs -> Env Term vars -> NF vars -> Glued vars
glueBack defs env nf
    = MkGlue False
             (do empty <- clearDefs defs
                 quote empty env nf)
             (const (pure nf))

export
glueClosure : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              Defs -> Env Term vars -> Closure vars -> Glued vars
glueClosure defs env clos
    = MkGlue False
             (do empty <- clearDefs defs
                 quote empty env clos)
             (const (evalClosure defs clos))

export
normalise : {auto c : Ref Ctxt Defs} ->
            {free : _} ->
            Defs -> Env Term free -> Term free -> Core (Term free)
normalise defs env tm = quote defs env !(nf defs env tm)

export
normaliseOpts : {auto c : Ref Ctxt Defs} ->
                {free : _} ->
                EvalOpts -> Defs -> Env Term free -> Term free -> Core (Term free)
normaliseOpts opts defs env tm
    = quote defs env !(nfOpts opts defs env tm)

export
normaliseHoles : {auto c : Ref Ctxt Defs} ->
                 {free : _} ->
                 Defs -> Env Term free -> Term free -> Core (Term free)
normaliseHoles defs env tm
    = quote defs env !(nfOpts withHoles defs env tm)

export
normaliseLHS : {auto c : Ref Ctxt Defs} ->
               {free : _} ->
               Defs -> Env Term free -> Term free -> Core (Term free)
normaliseLHS defs env (Bind fc n b sc)
    = pure $ Bind fc n b !(normaliseLHS defs (b :: env) sc)
normaliseLHS defs env tm
    = quote defs env !(nfOpts onLHS defs env tm)

export
tryNormaliseSizeLimit : {auto c : Ref Ctxt Defs} ->
                     {free : _} ->
                     Defs -> Nat ->
                     Env Term free -> Term free -> Core (Term free)
tryNormaliseSizeLimit defs limit env tm
    = do tm' <- nf defs env tm
         quoteOpts (MkQuoteOpts False False (Just limit)) defs env tm'

-- The size limit here is the depth of stuck applications. If it gets past
-- that size, return the original
export
normaliseSizeLimit : {auto c : Ref Ctxt Defs} ->
                     {free : _} ->
                     Defs -> Nat ->
                     Env Term free -> Term free -> Core (Term free)
normaliseSizeLimit defs limit env tm
    = catch (do tm' <- nf defs env tm
                quoteOpts (MkQuoteOpts False False (Just limit)) defs env tm')
            (\err => pure tm)

export
normaliseArgHoles : {auto c : Ref Ctxt Defs} ->
                    {free : _} ->
                    Defs -> Env Term free -> Term free -> Core (Term free)
normaliseArgHoles defs env tm
    = quote defs env !(nfOpts withArgHoles defs env tm)

export
normaliseAll : {auto c : Ref Ctxt Defs} ->
               {free : _} ->
               Defs -> Env Term free -> Term free -> Core (Term free)
normaliseAll defs env tm
    = quote defs env !(nfOpts withAll defs env tm)

-- Normalise, but without normalising the types of binders. Dealing with
-- binders is the slow part of normalisation so whenever we can avoid it, it's
-- a big win
export
normaliseScope : {auto c : Ref Ctxt Defs} ->
                 {free : _} ->
                 Defs -> Env Term free -> Term free -> Core (Term free)
normaliseScope defs env (Bind fc n b sc)
    = pure $ Bind fc n b !(normaliseScope defs (b :: env) sc)
normaliseScope defs env tm = normalise defs env tm

export
etaContract : {auto _ : Ref Ctxt Defs} ->
              {vars : _} -> Term vars -> Core (Term vars)
etaContract tm = do
  defs <- get Ctxt
  logTerm "eval.eta" 5 "Attempting to eta contract subterms of" tm
  nf <- normalise defs (mkEnv EmptyFC _) tm
  logTerm "eval.eta" 5 "Evaluated to" nf
  res <- mapTermM act tm
  logTerm "eval.eta" 5 "Result of eta-contraction" res
  pure res

   where

    act : {vars : _} -> Term vars -> Core (Term vars)
    act tm = do
      logTerm "eval.eta" 10 "  Considering" tm
      case tm of
        (Bind _ x (Lam _ _ _ _) (App _ fn (Local _ _ Z _))) => do
          logTerm "eval.eta" 10 "  Shrinking candidate" fn
          let shrunk = shrink fn (Drop Refl)
          case shrunk of
            Nothing => do
              log "eval.eta" 10 "  Failure!"
              pure tm
            Just tm' => do
              logTerm "eval.eta" 10 "  Success!" tm'
              pure tm'
        _ => pure tm

export
getValArity : Defs -> Env Term vars -> NF vars -> Core Nat
getValArity defs env (NBind fc x (Pi _ _ _ _) sc)
    = pure (S !(getValArity defs env !(sc defs (toClosure defaultOpts env (Erased fc Placeholder)))))
getValArity defs env val = pure 0

export
getArity : {auto c : Ref Ctxt Defs} ->
           {vars : _} ->
           Defs -> Env Term vars -> Term vars -> Core Nat
getArity defs env tm = getValArity defs env !(nf defs env tm)

-- Log message with a value, translating back to human readable names first
export
logNF : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        LogTopic -> Nat -> Lazy String -> Env Term vars -> NF vars -> Core ()
logNF s n msg env tmnf
    = when !(logging s n) $
        do defs <- get Ctxt
           tm <- logQuiet $ quote defs env tmnf
           tm' <- toFullNames tm
           depth <- getDepth
           logString depth s.topic n (msg ++ ": " ++ show tm')

-- Log message with a term, reducing holes and translating back to human
-- readable names first
export
logTermNF' : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             LogTopic ->
             Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
logTermNF' s n msg env tm
    = do defs <- get Ctxt
         tmnf <- logQuiet $ normaliseHoles defs env tm
         tm' <- toFullNames tmnf
         depth <- getDepth
         logString depth s.topic n (msg ++ ": " ++ show tm')

export
logTermNF : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            LogTopic ->
            Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
logTermNF s n msg env tm
    = when !(logging s n) $ logTermNF' s n msg env tm

export
logGlue : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          LogTopic ->
          Nat -> Lazy String -> Env Term vars -> Glued vars -> Core ()
logGlue s n msg env gtm
    = when !(logging s n) $
        do defs <- get Ctxt
           tm <- getTerm gtm
           tm' <- toFullNames tm
           depth <- getDepth
           logString depth s.topic n (msg ++ ": " ++ show tm')

export
logGlueNF : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            LogTopic ->
            Nat -> Lazy String -> Env Term vars -> Glued vars -> Core ()
logGlueNF s n msg env gtm
    = when !(logging s n) $
        do defs <- get Ctxt
           tm <- getTerm gtm
           tmnf <- logQuiet $ normaliseHoles defs env tm
           tm' <- toFullNames tmnf
           depth <- getDepth
           logString depth s.topic n (msg ++ ": " ++ show tm')

export
logEnv : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         LogTopic ->
         Nat -> String -> Env Term vars -> Core ()
logEnv s n msg env
    = when !(logging s n) $
        do depth <- getDepth
           logString depth s.topic n msg
           dumpEnv s env

  where

    dumpEnv : {vs : List Name} -> Env Term vs -> Core ()
    dumpEnv [] = pure ()
    dumpEnv {vs = x :: _} (Let _ c val ty :: bs)
        = do logTermNF' s n (msg ++ ": let " ++ show x) bs val
             logTermNF' s n (msg ++ ":" ++ show c ++ " " ++ show x) bs ty
             dumpEnv bs
    dumpEnv {vs = x :: _} (b :: bs)
        = do logTermNF' s n (msg ++ ":" ++ show (multiplicity b) ++ " " ++
                           show (piInfo b) ++ " " ++
                           show x) bs (binderType b)
             dumpEnv bs
replace' : {auto c : Ref Ctxt Defs} ->
           {vars : _} ->
           Int -> Defs -> Env Term vars ->
           (lhs : NF vars) -> (parg : Term vars) -> (exp : NF vars) ->
           Core (Term vars)
replace' {vars} tmpi defs env lhs parg tm
    = if !(convert defs env lhs tm)
         then pure parg
         else repSub tm
  where
    repArg : (Closure vars) -> Core (Term vars)
    repArg c
        = do tmnf <- evalClosure defs c
             replace' tmpi defs env lhs parg tmnf

    repSub : NF vars -> Core (Term vars)
    repSub (NBind fc x b scfn)
        = do b' <- traverse (\c => repSub !(evalClosure defs c)) b
             let x' = MN "tmp" tmpi
             sc' <- replace' (tmpi + 1) defs env lhs parg
                             !(scfn defs (toClosure defaultOpts env (Ref fc Bound x')))
             pure (Bind fc x b' (refsToLocals (Add x x' None) sc'))
    repSub (NApp fc hd [])
        = do empty <- clearDefs defs
             quote empty env (NApp fc hd [])
    repSub (NApp fc hd args)
        = do args' <- traverse (traversePair repArg) args
             pure $ applyStackWithFC
                        !(replace' tmpi defs env lhs parg (NApp fc hd []))
                        args'
    repSub (NDCon fc n t a args)
        = do args' <- traverse (traversePair repArg) args
             empty <- clearDefs defs
             pure $ applyStackWithFC
                        !(quote empty env (NDCon fc n t a []))
                        args'
    repSub (NTCon fc n t a args)
        = do args' <- traverse (traversePair repArg) args
             empty <- clearDefs defs
             pure $ applyStackWithFC
                        !(quote empty env (NTCon fc n t a []))
                        args'
    repSub (NAs fc s a p)
        = do a' <- repSub a
             p' <- repSub p
             pure (As fc s a' p')
    repSub (NDelayed fc r tm)
        = do tm' <- repSub tm
             pure (TDelayed fc r tm')
    repSub (NDelay fc r ty tm)
        = do ty' <- replace' tmpi defs env lhs parg !(evalClosure defs ty)
             tm' <- replace' tmpi defs env lhs parg !(evalClosure defs tm)
             pure (TDelay fc r ty' tm')
    repSub (NForce fc r tm args)
        = do args' <- traverse (traversePair repArg) args
             tm' <- repSub tm
             pure $ applyStackWithFC (TForce fc r tm') args'
    repSub (NErased fc (Dotted t))
        = do t' <- repSub t
             pure (Erased fc (Dotted t'))
    repSub tm = do empty <- clearDefs defs
                   quote empty env tm

export
replace : {auto c : Ref Ctxt Defs} ->
          {vars : _} ->
          Defs -> Env Term vars ->
          (orig : NF vars) -> (new : Term vars) -> (tm : NF vars) ->
          Core (Term vars)
replace = replace' 0

-- If the term is an application of a primitive conversion (fromInteger etc)
-- and it's applied to a constant, fully normalise the term.
export
normalisePrims : {auto c : Ref Ctxt Defs} -> {vs : _} ->
                 -- size heuristic for when to unfold
                 (Constant -> Bool) ->
                 -- view to check whether an argument is a constant
                 (arg -> Maybe Constant) ->
                 -- Reduce everything (True) or just public export (False)
                 Bool ->
                 -- list of primitives
                 List Name ->
                 -- view of the potential redex
                 (n : Name) ->          -- function name
                 (args : List arg) ->   -- arguments from inside out (arg1, ..., argk)
                 -- actual term to evaluate if needed
                 (tm : Term vs) ->      -- original term (n arg1 ... argk)
                 Env Term vs ->         -- evaluation environment
                 -- output only evaluated if primitive
                 Core (Maybe (Term vs))
normalisePrims boundSafe viewConstant all prims n args tm env
   = do let True = isPrimName prims !(getFullName n) -- is a primitive
              | _ => pure Nothing
        let (mc :: _) = reverse args -- with at least one argument
              | _ => pure Nothing
        let (Just c) = viewConstant mc -- that is a constant
              | _ => pure Nothing
        let True = boundSafe c -- that we should expand
              | _ => pure Nothing
        defs <- get Ctxt
        tm <- if all
                 then normaliseAll defs env tm
                 else normalise defs env tm
        pure (Just tm)
