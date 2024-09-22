module Core.Normalise.Eval

import Core.Case.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Primitives
import Core.TT
import Core.Value

import Data.List
import Data.SnocList
import Data.Maybe
import Data.Nat
import Data.String
import Data.Vect

import Libraries.Data.WithDefault

%default covering

-- A pair of a term and its normal form. This could be constructed either
-- from a term (via 'gnf') or a normal form (via 'glueBack') but the other
-- part will only be constructed when needed, because it's in Core.
public export
data Glued : SnocList Name -> Type where
     MkGlue : (fromTerm : Bool) -> -- is it built from the term; i.e. can
                                   -- we read the term straight back?
              Core (Term vars) -> (Ref Ctxt Defs -> Core (NF vars)) -> Glued vars

export
isFromTerm : Glued vars -> Bool
isFromTerm (MkGlue ft _ _) = ft

export
getTerm : Glued vars -> Core (Term vars)
getTerm (MkGlue _ tm _) = tm

export
getNF : {auto c : Ref Ctxt Defs} -> Glued vars -> Core (NF vars)
getNF {c} (MkGlue _ _ nf) = nf c

public export
Stack : SnocList Name -> Type
Stack vars = List (FC, Closure vars)

evalWithOpts : {auto c : Ref Ctxt Defs} ->
               {free, vars : _} ->
               Defs -> EvalOpts ->
               Env Term free -> LocalEnv free vars ->
               Term (free ++ vars) -> Stack free -> Core (NF free)

export
evalClosure : {auto c : Ref Ctxt Defs} ->
              {free : _} -> Defs -> Closure free -> Core (NF free)

export
evalArg : {auto c : Ref Ctxt Defs} -> {free : _} -> Defs -> Closure free -> Core (NF free)
evalArg defs c = evalClosure defs c

export
toClosure : EvalOpts -> Env Term outer -> Term outer -> Closure outer
toClosure opts env tm = MkClosure opts [] env tm

updateLimit : NameType -> Name -> EvalOpts -> Core (Maybe EvalOpts)
updateLimit Func n opts
    = pure $ if isNil (reduceLimit opts)
         then Just opts
         else case lookup n (reduceLimit opts) of
                   Nothing => Nothing
                   Just Z => Nothing
                   Just (S k) =>
                      Just ({ reduceLimit $= set n k } opts)
  where
    set : Name -> Nat -> List (Name, Nat) -> List (Name, Nat)
    set n v [] = []
    set n v ((x, l) :: xs)
        = if x == n
             then (x, v) :: xs
             else (x, l) :: set n v xs
updateLimit t n opts = pure (Just opts)

data CaseResult a
     = Result a
     | NoMatch -- case alternative didn't match anything
     | GotStuck -- alternative matched, but got stuck later

record TermWithEnv (free : SnocList Name) where
    constructor MkTermEnv
    { varsEnv : SnocList Name }
    locEnv : LocalEnv free varsEnv
    term : Term $ free ++ varsEnv

parameters (defs : Defs) (topopts : EvalOpts)
  mutual
    eval : {auto c : Ref Ctxt Defs} ->
           {free, vars : _} ->
           Env Term free -> LocalEnv free vars ->
           Term (free ++ vars) -> Stack free -> Core (NF free)
    eval env locs (Local fc mrig idx prf) stk
        = logDepth $ evalLocal env fc mrig idx prf stk locs
    eval env locs (Ref fc nt fn) stk
        =
            let scoped_list_stk = fromList stk
            in evalRef env False fc nt fn scoped_list_stk (NApp fc (NRef nt fn) scoped_list_stk)
    eval {vars} {free} env locs (Meta fc name idx args) stk
        = evalMeta env fc name idx (closeArgs args) stk
      where
        -- Yes, it's just a map, but specialising it by hand since we
        -- use this a *lot* and it saves the run time overhead of making
        -- a closure and calling APPLY.
        closeArgs : List (Term (free ++ vars)) -> SnocList (Closure free)
        closeArgs [] = [<]
        closeArgs (t :: ts) = closeArgs ts :< MkClosure topopts locs env t
    eval env locs (Bind fc x (Lam _ r _ ty) scope) (thunk :: stk)
        = eval env (snd thunk :: locs) scope stk
    eval env locs (Bind fc x b@(Let _ r val ty) scope) stk
        = if (holesOnly topopts || argHolesOnly topopts) && not (tcInline topopts)
             then do let b' = map (MkClosure topopts locs env) b
                     pure $ NBind fc x b'
                        (\defs', arg => evalWithOpts defs' topopts
                                                env (arg :: locs) scope stk)
             else eval env (MkClosure topopts locs env val :: locs) scope stk
    eval env locs (Bind fc x b scope) stk
        = do let b' = map (MkClosure topopts locs env) b
             pure $ NBind fc x b'
                      (\defs', arg => evalWithOpts defs' topopts
                                              env (arg :: locs) scope stk)
    eval env locs (App fc fn arg) stk
        = case strategy topopts of
               CBV => do arg' <- eval env locs arg []
                         eval env locs fn ((fc, MkNFClosure topopts env arg') :: stk)
               CBN => eval env locs fn ((fc, MkClosure topopts locs env arg) :: stk)
    eval env locs (As fc s n tm) stk
        = if removeAs topopts
             then eval env locs tm stk
             else do n' <- eval env locs n stk
                     tm' <- eval env locs tm stk
                     pure (NAs fc s n' tm')
    eval env locs (TDelayed fc r ty) stk
        = do ty' <- eval env locs ty stk
             pure (NDelayed fc r ty')
    eval env locs (TDelay fc r ty tm) stk
        = pure (NDelay fc r (MkClosure topopts locs env ty)
                            (MkClosure topopts locs env tm))
    eval env locs (TForce fc r tm) stk
        = do tm' <- eval env locs tm []
             case tm' of
                  NDelay fc r _ arg =>
                      eval env (arg :: locs) (Local {name = UN (Basic "fvar")} fc Nothing _ First) stk
                  _ => pure (NForce fc r tm' (fromList stk))
    eval env locs (PrimVal fc c) stk = pure $ NPrimVal fc c
    eval env locs (Erased fc a) stk
      = NErased fc <$> traverse @{%search} @{CORE} (\ t => eval env locs t stk) a
    eval env locs (TType fc u) stk = pure $ NType fc u

    -- Apply an evaluated argument (perhaps cached from an earlier evaluation)
    -- to a stack
    export
    applyToStack : {auto c : Ref Ctxt Defs} ->
                   {free : _} ->
                   Env Term free ->
                   NF free -> Stack free -> Core (NF free)
    applyToStack env (NBind fc _ (Lam _ _ _ _) sc) (arg :: stk)
        = do arg' <- sc defs $ snd arg
             applyToStack env arg' stk
    applyToStack env (NBind fc x b@(Let _ r val ty) sc) stk
        = if (holesOnly topopts || argHolesOnly topopts) && not (tcInline topopts)
             then pure (NBind fc x b
                              (\defs', arg => applyToStack env !(sc defs' arg) stk))
             else applyToStack env !(sc defs val) stk
    applyToStack env (NBind fc x b sc) stk
        = pure (NBind fc x b
                      (\defs', arg => applyToStack env !(sc defs' arg) stk))
    applyToStack env (NApp fc (NRef nt fn) args) stk
        =
            let combined_stack = args <>< stk
            in evalRef env False fc nt fn combined_stack
                  (NApp fc (NRef nt fn) combined_stack)
    applyToStack env (NApp fc (NLocal mrig idx p) args) stk
        = evalLocal env fc mrig _ p (args <>> stk) []
    applyToStack env (NApp fc (NMeta n i args) args') stk
        = evalMeta env fc n i args (args' <>> stk)
    applyToStack env (NDCon fc n t a args) stk
        = pure $ NDCon fc n t a (args <>< stk)
    applyToStack env (NTCon fc n t a args) stk
        = pure $ NTCon fc n t a (args <>< stk)
    applyToStack env (NAs fc s p t) stk
       = if removeAs topopts
            then applyToStack env t stk
            else do p' <- applyToStack env p []
                    t' <- applyToStack env t stk
                    pure (NAs fc s p' t')
    applyToStack env (NDelayed fc r tm) stk
       = do tm' <- applyToStack env tm stk
            pure (NDelayed fc r tm')
    applyToStack env nf@(NDelay fc r ty tm) stk
       = pure nf -- stack should always be empty here!
    applyToStack env (NForce fc r tm args) stk
       = do tm' <- applyToStack env tm []
            case tm' of
                 NDelay fc r _ arg =>
                    eval env [arg] (Local {name = UN (Basic "fvar")} fc Nothing _ First) stk
                 _ => pure (NForce fc r tm' (args <>< stk))
    applyToStack env nf@(NPrimVal fc _) _ = pure nf
    applyToStack env (NErased fc a) stk
      = NErased fc <$> traverse @{%search} @{CORE} (\ t => applyToStack env t stk) a
    applyToStack env nf@(NType fc _) _ = pure nf

    evalLocClosure : {auto c : Ref Ctxt Defs} ->
                     {free : _} ->
                     Env Term free ->
                     FC -> Maybe Bool ->
                     Stack free ->
                     Closure free ->
                     Core (NF free)
    evalLocClosure env fc mrig stk (MkClosure opts locs' env' tm')
        = evalWithOpts defs opts env' locs' tm' stk
    evalLocClosure {free} env fc mrig stk (MkNFClosure opts env' nf)
        = applyToStack env' nf stk

    evalLocal : {auto c : Ref Ctxt Defs} ->
                {free : _} ->
                Env Term free ->
                FC -> Maybe Bool ->
                (idx : Nat) -> (0 p : IsVar nm idx (free ++ vars)) ->
                Stack free ->
                LocalEnv free vars ->
                Core (NF free)
    -- If it's one of the free variables, we are done unless the free
    -- variable maps to a let-binding
    evalLocal env fc mrig idx prf stk []
        = if not (holesOnly topopts || argHolesOnly topopts)
             -- if we know it's not a let, no point in even running `getBinder`
             && fromMaybe True mrig
             then
               case getBinder prf env of
                    Let _ _ val _ => eval env [] val stk
                    _ => pure $ NApp fc (NLocal mrig idx prf) (fromList stk)
             else pure $ NApp fc (NLocal mrig idx prf) (fromList stk)
    evalLocal env fc mrig Z First stk (x :: locs)
        = evalLocClosure env fc mrig stk x
    evalLocal {vars = xs :< x} {free}
              env fc mrig (S idx) (Later p) stk (_ :: locs)
        = evalLocal {vars = xs} env fc mrig idx p stk locs

    updateLocal : EvalOpts -> Env Term free ->
                  (idx : Nat) -> (0 p : IsVar nm idx (free ++ vars)) ->
                  LocalEnv free vars -> NF free ->
                  LocalEnv free vars
    updateLocal opts env Z First (x :: locs) nf
        = MkNFClosure opts env nf :: locs
    updateLocal opts env (S idx) (Later p) (x :: locs) nf
        = x :: updateLocal opts env idx p locs nf
    updateLocal _ _ _ _ locs nf = locs

    evalMeta : {auto c : Ref Ctxt Defs} ->
               {free : _} ->
               Env Term free ->
               FC -> Name -> Int -> SnocList (Closure free) ->
               Stack free -> Core (NF free)
    evalMeta env fc nm i args stk
        = let
              args' = if isNil stk then map (EmptyFC,) args
                         else (map (EmptyFC,) args) <>< stk
                        in
              evalRef env True fc Func (Resolved i) args'
                          (NApp fc (NMeta nm i args) (fromList scoped_list_stack))

    -- The commented out logging here might still be useful one day, but
    -- evalRef is used a lot and even these tiny checks turn out to be
    -- worth skipping if we can
    evalRef : {auto c : Ref Ctxt Defs} ->
              {free : _} ->
              Env Term free ->
              (isMeta : Bool) ->
              FC -> NameType -> Name -> SnocList (FC, Closure free) -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalRef env meta fc (DataCon tag arity) fn stk def
        = do -- logC "eval.ref.data" 50 $ do fn' <- toFullNames fn -- Can't use ! here, it gets lifted too far
             --                             pure $ "Found data constructor: " ++ show fn'
             pure $ NDCon fc fn tag arity stk
    evalRef env meta fc (TyCon tag arity) fn stk def
        = do -- logC "eval.ref.type" 50 $ do fn' <- toFullNames fn
             --                             pure $ "Found type constructor: " ++ show fn'
             pure $ ntCon fc fn tag arity stk
    evalRef env meta fc Bound fn stk def
        = do -- logC "eval.ref.bound" 50 $ do fn' <- toFullNames fn
             --                              pure $ "Found bound variable: " ++ show fn'
             pure def
    evalRef env meta fc nt@Func n stk def
        = do -- logC "eval.ref" 50 $ do n' <- toFullNames n
             --                        pure $ "Found function: " ++ show n'
             Just res <- lookupCtxtExact n (gamma defs)
                  | Nothing => do logC "eval.stuck.outofscope" 5 $ do n' <- toFullNames n
                                                                      pure $ "Stuck function: " ++ show n'
                                  pure def
             let redok1 = evalAll topopts
             let redok2 = reducibleInAny (currentNS defs :: nestedNS defs)
                                         (fullname res)
                                         (collapseDefault $ visibility res)
             -- want to shortcut that second check, if we're evaluating
             -- everything, so don't let bind unless we need that log!
             let redok = redok1 || redok2
             checkTimer -- If we're going to time out anywhere, it'll be
                        -- when evaluating something recursive, so this is a
                        -- good place to check
             unless redok2 $ logC "eval.stuck" 5 $ do n' <- toFullNames n
                                                      pure $ "Stuck function: \{show n'}"
             if redok
                then do
                   Just opts' <- updateLimit nt n topopts
                        | Nothing => do log "eval.stuck" 10 $ "Function \{show n} past reduction limit"
                                        pure def -- name is past reduction limit
                   nf <- evalDef env opts' meta fc
                           (multiplicity res) (definition res) (flags res) stk def
                   -- logC "eval.ref" 50 $ do n' <- toFullNames n
                   --                         nf <- toFullNames nf
                   --                         pure "Reduced \{show n'} to \{show nf}"
                   pure nf
                else pure def

    getCaseBound : SnocList (Closure free) ->
                   (args : SnocList Name) ->
                   LocalEnv free more ->
                   Maybe (LocalEnv free (more ++ args))
    getCaseBound [<]            [<]      loc = Just loc
    getCaseBound [<]            (_ :< _)  loc = Nothing -- mismatched arg length
    getCaseBound (args :< arg) [<]      loc = Nothing -- mismatched arg length
    getCaseBound (args :< arg) (ns :< n) loc = (arg ::) <$> (getCaseBound args ns loc)

    -- Returns the case term from the matched pattern with the LocalEnv (arguments from constructor pattern ConCase)
    evalConAlt : {auto c : Ref Ctxt Defs} ->
                 {more, free : _} ->
                 Env Term free ->
                 LocalEnv free more -> EvalOpts -> FC ->
                 Stack free ->
                 (args : SnocList Name) ->
                 SnocList (Closure free) ->
                 CaseTree (more ++ args) ->
                 Core (CaseResult (TermWithEnv free))
    evalConAlt env loc opts fc stk args args' sc
         = do let Just bound = getCaseBound args' args loc
                   | Nothing => pure GotStuck
              evalTree env bound opts fc stk sc

    tryAlt : {auto c : Ref Ctxt Defs} ->
             {free, more : _} ->
             Env Term free ->
             LocalEnv free more -> EvalOpts -> FC ->
             Stack free -> NF free -> CaseAlt more ->
             Core (CaseResult (TermWithEnv free))
    -- Dotted values should still reduce at compile time
    tryAlt {more} env loc opts fc stk (NErased _ (Dotted tm)) alt
         = tryAlt {more} env loc opts fc stk tm alt
    -- Ordinary constructor matching
    tryAlt {more} env loc opts fc stk (NDCon _ nm tag' arity args') (ConCase x tag args sc)
         = if tag == tag'
              then evalConAlt env loc opts fc stk args (map snd args') sc
              else pure NoMatch
    -- Type constructor matching, in typecase
    tryAlt {more} env loc opts fc stk (NTCon _ nm tag' arity args') (ConCase nm' tag args sc)
         = if nm == nm'
              then evalConAlt env loc opts fc stk args (map snd args') sc
              else pure NoMatch
    -- Primitive type matching, in typecase
    tryAlt env loc opts fc stk (NPrimVal _ c) (ConCase nm tag args sc)
         = case args of -- can't just test for it in the `if` for typing reasons
             [<] => if UN (Basic $ show c) == nm
                   then evalTree env loc opts fc stk sc
                   else pure NoMatch
             _ => pure NoMatch
    -- Type of type matching, in typecase
    tryAlt env loc opts fc stk (NType _ _) (ConCase (UN (Basic "Type")) tag [<] sc)
         = evalTree env loc opts fc stk sc
    tryAlt env loc opts fc stk (NType _ _) (ConCase _ _ _ _)
         = pure NoMatch
    -- Arrow matching, in typecase
    tryAlt {more}
           env loc opts fc stk (NBind pfc x (Pi fc' r e aty) scty) (ConCase (UN (Basic "->")) tag [<t, s] sc)
       = evalConAlt {more} env loc opts fc stk [<t, s]
                  [<MkNFClosure opts env (NBind pfc x (Lam fc' r e aty) scty), aty]
                  sc
    tryAlt {more}
           env loc opts fc stk (NBind pfc x (Pi fc' r e aty) scty) (ConCase nm tag args sc)
       = pure NoMatch
    -- Delay matching
    tryAlt env loc opts fc stk (NDelay _ _ ty arg) (DelayCase tyn argn sc)
         = evalTree env (ty :: arg :: loc) opts fc stk sc
    -- Constant matching
    tryAlt env loc opts fc stk (NPrimVal _ c') (ConstCase c sc)
         = if c == c' then evalTree env loc opts fc stk sc
                      else pure NoMatch
    -- Default case matches against any *concrete* value
    tryAlt env loc opts fc stk val (DefaultCase sc)
         = if concrete val
              then evalTree env loc opts fc stk sc
              else pure GotStuck
      where
        concrete : NF free -> Bool
        concrete (NDCon _ _ _ _ _) = True
        concrete (NTCon _ _ _ _ _) = True
        concrete (NPrimVal _ _) = True
        concrete (NBind _ _ _ _) = True
        concrete (NType _ _) = True
        concrete (NDelay _ _ _ _) = True
        concrete _ = False
    tryAlt _ _ _ _ _ _ _ = pure GotStuck

    findAlt : {auto c : Ref Ctxt Defs} ->
              {args, free : _} ->
              Env Term free ->
              LocalEnv free args -> EvalOpts -> FC ->
              Stack free -> NF free -> List (CaseAlt args) ->
              Core (CaseResult (TermWithEnv free))
    findAlt env loc opts fc stk val [] = do
      log "eval.casetree.stuck" 2 "Ran out of alternatives"
      pure GotStuck
    findAlt env loc opts fc stk val (x :: xs)
         = do res@(Result {}) <- tryAlt env loc opts fc stk val x
                   | NoMatch => findAlt env loc opts fc stk val xs
                   | GotStuck => do
                       logC "eval.casetree.stuck" 5 $ do
                         val <- toFullNames val
                         x <- toFullNames x
                         pure $ "Got stuck matching \{show val} against \{show x}"
                       pure GotStuck
              pure res

    evalTree : {auto c : Ref Ctxt Defs} ->
               {args, free : _} -> Env Term free -> LocalEnv free args ->
               EvalOpts -> FC ->
               Stack free -> CaseTree args ->
               Core (CaseResult (TermWithEnv free))
    evalTree env loc opts fc stk (Case {name} idx x _ alts)
      = do xval <- evalLocal env fc Nothing idx (embedIsVar x) [] loc
           -- we have not defined quote yet (it depends on eval itself) so we show the NF
           -- i.e. only the top-level constructor.
           logC "eval.casetree" 5 $ do
             xval <- toFullNames xval
             pure "Evaluated \{show name} to \{show xval}"
           let loc' = updateLocal opts env idx (embedIsVar x) loc xval
           findAlt env loc' opts fc stk xval alts
    evalTree env loc opts fc stk (STerm _ tm)
          = pure (Result $ MkTermEnv loc $ embed tm)
    evalTree env loc opts fc stk _ = pure GotStuck

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> SnocList (FC, Closure free) ->
                    Maybe (Vect arity (Closure free), SnocList (FC, Closure free))
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> SnocList (FC, Closure free) ->
                  Vect got (Closure free) ->
                  Maybe (Vect (got + remain) (Closure free), SnocList (FC, Closure free))
        takeStk {got} Z stk acc = Just (rewrite plusZeroRightNeutral got in
                                    reverse acc, stk)
        takeStk (S k) [<] acc = Nothing
        takeStk {got} (S k) (stk :< arg) acc
           = rewrite sym (plusSuccRightSucc got k) in
                     takeStk k stk (snd arg :: acc)

    argsFromStack : (args : SnocList Name) ->
                    SnocList (FC, Closure free) ->
                    Maybe (LocalEnv free args, SnocList (FC, Closure free))
    argsFromStack [<] stk = Just ([], stk)
    argsFromStack (ns :< n) [<] = Nothing
    argsFromStack (ns :< n) (args :< arg)
         = do (loc', stk') <- argsFromStack ns args
              pure (snd arg :: loc', stk')

    evalOp : {auto c : Ref Ctxt Defs} ->
             {arity, free : _} ->
             (Vect arity (NF free) -> Maybe (NF free)) ->
             SnocList (FC, Closure free) -> (def : Lazy (NF free)) ->
             Core (NF free)
    evalOp {arity} fn stk def
        = case takeFromStack arity stk of
               -- Stack must be exactly the right height
               Just (args, [<]) =>
                  do argsnf <- evalAll args
                     pure $ case fn argsnf of
                          Nothing => def
                          Just res => res
               _ => pure def
      where
        -- No traverse for Vect in Core...
        evalAll : Vect n (Closure free) -> Core (Vect n (NF free))
        evalAll [] = pure []
        evalAll (c :: cs) = pure $ !(evalClosure defs c) :: !(evalAll cs)

    evalDef : {auto c : Ref Ctxt Defs} ->
              {free : _} ->
              Env Term free -> EvalOpts ->
              (isMeta : Bool) -> FC ->
              RigCount -> Def -> List DefFlag ->
              SnocList (FC, Closure free) -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalDef env opts meta fc rigd (PMDef r args tree _ _) flags stk def
       -- If evaluating the definition fails (e.g. due to a case being
       -- stuck) return the default.
       -- We can use the definition if one of the following is true:
       --   + The 'alwayReduce' flag (r) is set
       --   + We're not in 'holesOnly', 'argHolesOnly' or 'tcInline'
       --         (that's the default mode)
       --   + It's a metavariable and not in Rig0
       --   + It's a metavariable and we're not in 'argHolesOnly'
       --   + It's inlinable and we're in 'tcInline'
        = if alwaysReduce r
             || (not (holesOnly opts || argHolesOnly opts || tcInline opts))
             || (meta && not (isErased rigd))
             || (meta && holesOnly opts)
             || (tcInline opts && elem TCInline flags)
             then case argsFromStack args stk of
                       Nothing => do logC "eval.def.underapplied" 50 $ do
                                       def <- toFullNames def
                                       pure "Cannot reduce under-applied \{show def}"
                                     pure def
                       Just (locs', stk') =>
                            do (Result (MkTermEnv newLoc res)) <- evalTree env locs' opts fc (toList stk') tree
                                    | _ => do logC "eval.def.stuck" 50 $ do
                                                def <- toFullNames def
                                                pure "evalTree failed on \{show def}"
                                              pure def
                               case fuel opts of
                                    Nothing => evalWithOpts defs opts env newLoc res (toList stk')
                                    Just Z => log "eval.def.stuck" 50 "Recursion depth limit exceeded"
                                              >> pure def
                                    Just (S k) =>
                                        do let opts' = { fuel := Just k } opts
                                           evalWithOpts defs opts' env newLoc res (toList stk')
             else do -- logC "eval.def.stuck" 50 $ do
                     --   def <- toFullNames def
                     --   pure $ unlines [ "Refusing to reduce \{show def}:"
                     --                  , "  holesOnly   : \{show $ holesOnly opts}"
                     --                  , "  argHolesOnly: \{show $ argHolesOnly opts}"
                     --                  , "  tcInline    : \{show $ tcInline opts}"
                     --                  , "  meta        : \{show meta}"
                     --                  , "  rigd        : \{show rigd}"
                     --                  ]
                     pure def
    evalDef env opts meta fc rigd (Builtin op) flags stk def
        = evalOp (getOp op) stk def
    -- All other cases, use the default value, which is already applied to
    -- the stack
    evalDef env opts meta fc rigd def flags stk orig = do
      logC "eval.def.stuck" 50 $ do
        orig <- toFullNames orig
        pure "Cannot reduce def \{show orig}: it is a \{show def}"
      pure orig

-- Make sure implicit argument order is right... 'vars' is used so we'll
-- write it explicitly, but it does appear after the parameters in 'eval'!
evalWithOpts {vars} defs opts = eval {vars} defs opts

evalClosure defs (MkClosure opts locs env tm)
    = eval defs opts env locs tm []
evalClosure defs (MkNFClosure opts env nf)
    = applyToStack defs opts env nf []

export
evalClosureWithOpts : {auto c : Ref Ctxt Defs} ->
                      {free : _} ->
                      Defs -> EvalOpts -> Closure free -> Core (NF free)
evalClosureWithOpts defs opts (MkClosure _ locs env tm)
    = eval defs opts env locs tm []
evalClosureWithOpts defs opts (MkNFClosure _ env nf)
    = applyToStack defs opts env nf []

export
nf : {auto c : Ref Ctxt Defs} ->
     {vars : _} ->
     Defs -> Env Term vars -> Term vars -> Core (NF vars)
nf defs env tm = logDepth $ eval defs defaultOpts env [] tm []

export
nfOpts : {auto c : Ref Ctxt Defs} ->
         {vars : _} ->
         EvalOpts -> Defs -> Env Term vars -> Term vars -> Core (NF vars)
nfOpts opts defs env tm = logDepth $ eval defs opts env [] tm []

export
gnf : {vars : _} ->
      Env Term vars -> Term vars -> Glued vars
gnf env tm
    = MkGlue True
             (pure tm)
             (\c => do defs <- get Ctxt
                       nf defs env tm)

export
gnfOpts : {vars : _} ->
          EvalOpts -> Env Term vars -> Term vars -> Glued vars
gnfOpts opts env tm
    = MkGlue True
             (pure tm)
             (\c => do defs <- get Ctxt
                       nfOpts opts defs env tm)

export
gType : FC -> Name -> Glued vars
gType fc u = MkGlue True (pure (TType fc u)) (const (pure (NType fc u)))

export
gErased : FC -> Glued vars
gErased fc = MkGlue True (pure (Erased fc Placeholder)) (const (pure (NErased fc Placeholder)))

-- Resume a previously blocked normalisation with a new environment
export
continueNF : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Defs -> Env Term vars -> NF vars -> Core (NF vars)
continueNF defs env stuck
   = applyToStack defs defaultOpts env stuck []
