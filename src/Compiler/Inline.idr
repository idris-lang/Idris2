module Compiler.Inline

import Compiler.CaseOpts
import Compiler.CompileExpr
import Compiler.Opts.ConstantFold
import Compiler.Opts.Identity
import Compiler.Opts.InlineHeuristics

import Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.FC
import Core.Hash
import Core.Options
import Core.TT

import Data.Maybe
import Data.List
import Data.SnocList
import Data.Vect
import Libraries.Data.List.LengthMatch
import Libraries.Data.NameMap
import Libraries.Data.WithDefault

import Libraries.Data.SnocList.LengthMatch
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.HasLength

%default covering

data EEnv : SnocList Name -> SnocList Name -> Type where
     Lin : EEnv free [<]
     (:<) : EEnv free vars -> CExp free -> EEnv free (vars :< x)

public export
covering
{free, vars : _} -> Show (EEnv free vars) where
    show x = "EEnv [" ++ showAll x ++ "]{vars = " ++ show (toList vars) ++ ", free = " ++ show (toList free) ++ "}"
        where
            showAll : {free, vars : _} -> EEnv free vars -> String
            showAll Lin = ""
            showAll (Lin :< x) = show x
            showAll (xx :< x) = show x ++ ", " ++ showAll xx

extend : EEnv free vars -> (args : SnocList (CExp free)) -> (args' : SnocList Name) ->
         LengthMatch args args' -> EEnv free (vars ++ args')
extend env [<] [<] LinMatch = env
extend env (xs :< a) (ns :< n) (SnocMatch w)
    = extend env xs ns w :< a

Stack : SnocList Name -> Type
Stack vars = List (CExp vars)

unload : Stack vars -> CExp vars -> CExp vars
unload [] e = e
unload (a :: args) e = unload args (CApp (getFC e) e [a])

unloadApp : Nat -> Stack vars -> CExp vars -> CExp vars
unloadApp n args e = unload (drop n args) (CApp (getFC e) e (take n args))

getArity : CDef -> Nat
getArity (MkFun args _) = length args
getArity (MkCon _ arity _) = arity
getArity (MkForeign _ args _) = length args
getArity (MkError _) = 0

takeFromStack : EEnv free vars -> Stack free -> (args : SnocList Name) ->
                Maybe (EEnv free (vars ++ args), Stack free)
takeFromStack env (e :: es) (as :< a)
  = do (env', stk') <- takeFromStack env es as
       pure (env' :< e, stk')
takeFromStack env stk [<] = pure (env, stk)
takeFromStack env [] args = Nothing

data LVar : Type where

genName : {auto l : Ref LVar Int} ->
          String -> Core Name
genName n
    = do i <- get LVar
         put LVar (i + 1)
         pure (MN n i)

refToLocal : Name -> (x : Name) -> CExp vars -> CExp (vars :< x)
refToLocal x new tm = refsToLocals (Add new x None) tm

largest : Ord a => a -> List a -> a
largest x [] = x
largest x (y :: ys)
    = if y > x
         then largest y ys
         else largest x ys

mutual
  used : {free : _} ->
         {idx : Nat} -> (0 p : IsVar n idx free) -> CExp free -> Int
  used {idx} n (CLocal _ {idx=pidx} prf) = if idx == pidx then 1 else 0
  used n (CLam _ _ sc) = used (Later n) sc
  used n (CLet _ _ NotInline val sc)
      = let usedl = used n val + used (Later n) sc in
            if usedl > 0
               then 1000 -- Don't do any inlining of the name, because if it's
                         -- used under a non-inlinable let things might go wrong
               else usedl
  used n (CLet _ _ YesInline val sc) = used n val + used (Later n) sc
  used n (CApp _ x args) = foldr (+) (used n x) (map (used n) args)
  used n (CCon _ _ _ _ args) = foldr (+) 0 (map (used n) args)
  used n (COp _ _ args) = foldr (+) 0 (map (used n) args)
  used n (CExtPrim _ _ args) = foldr (+) 0 (map (used n) args)
  used n (CForce _ _ x) = used n x
  used n (CDelay _ _ x) = used n x
  used n (CConCase fc sc alts def)
     = used n sc +
          largest (maybe 0 (used n) def) (map (usedCon n) alts)
  used n (CConstCase fc sc alts def)
     = used n sc +
          largest (maybe 0 (used n) def) (map (usedConst n) alts)
  used _ tm = 0

  usedCon : {free : _} ->
            {idx : Nat} -> (0 p : IsVar n idx free) -> CConAlt free -> Int
  usedCon n (MkConAlt _ _ _ args sc)
      = let MkVar n' = weakenNs (mkSizeOf args) (MkVar n) in
            used n' sc

  usedConst : {free : _} ->
              {idx : Nat} -> (0 p : IsVar n idx free) -> CConstAlt free -> Int
  usedConst n (MkConstAlt _ sc) = used n sc

mutual
  evalLocal : {vars, free : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto l : Ref LVar Int} ->
              FC -> List Name -> Stack free ->
              EEnv free vars ->
              {idx : Nat} -> (0 p : IsVar x idx (free ++ vars)) ->
              Core (CExp free)
  evalLocal {vars = [<]} fc rec stk env p
      = pure $ unload stk (CLocal fc p)
  evalLocal {vars = xs :< x} fc rec stk (env :< v) First
      = case stk of
             [] => pure v
             _ => eval rec env stk (weakenNs (mkSizeOf xs) v)
  evalLocal {vars = xs :< x} fc rec stk (env :< _) (Later p)
      = evalLocal fc rec stk env p

  tryApply : {vars, free : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto l : Ref LVar Int} ->
             List Name -> Stack free -> EEnv free vars -> CDef ->
             Core (Maybe (CExp free))
  tryApply {free} {vars} rec stk env (MkFun args exp)
      = do let Just (env', stk') = takeFromStack env stk args
               | Nothing => pure Nothing
           res <- eval rec env' stk'
                     (rewrite appendAssociative free vars args in
                              -- Yaffle: embed {vars = free ++ vars} exp
                              embed {outer = free ++ vars} exp)
           pure (Just res)
  tryApply rec stk env _ = pure Nothing

  eval : {vars, free : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto l : Ref LVar Int} ->
         List Name -> EEnv free vars -> Stack free -> CExp (free ++ vars) ->
         Core (CExp free)
  eval rec env stk (CLocal fc p) = evalLocal fc rec stk env p
  -- This is hopefully a temporary hack, giving a special case for io_bind.
  -- Currently the elaborator is a bit cautious about inlining case blocks
  -- in case they duplicate work. We should fix that, to decide more accurately
  -- whether they're safe to inline, but until then this gives such a huge
  -- boost by removing unnecessary lambdas that we'll keep the special case.
  eval rec env stk (CRef fc n) = do
        when (n == NS primIONS (UN $ Basic "io_bind")) $
          log "compiler.inline.io_bind" 50 $
            "Attempting to inline io_bind, its stack is: \{show stk}"
        case (n == NS primIONS (UN $ Basic "io_bind"), stk) of
          (True, act :: cont :: world :: stk) =>
                 do xn <- genName "act"
                    sc <- eval rec [<] [] (CApp fc cont [CRef fc xn, world])
                    pure $ unload stk $
                             CLet fc xn NotInline
                               (CApp fc act [world])
                               (refToLocal xn xn sc)
          (True, [act, cont]) =>
                 do wn <- genName "world"
                    xn <- genName "act"
                    let world : forall vars. CExp vars := CRef fc wn
                    sc <- eval rec [<] [] (CApp fc cont [CRef fc xn, world])
                    pure $ CLam fc wn
                         $ refToLocal wn wn
                         $ CLet fc xn NotInline (CApp fc act [world])
                         $ refToLocal xn xn
                         $ sc
          (_,_) =>
             do defs <- get Ctxt
                Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure (unload stk (CRef fc n))
                let Just def = compexpr gdef
                  | Nothing => pure (unload stk (CRef fc n))
                let arity = getArity def
                let gdefFlags = flags gdef
                if (Inline `elem` gdefFlags)
                    && (not (n `elem` rec))
                    && (not (NoInline `elem` gdefFlags))
                   then do ap <- tryApply (n :: rec) stk env def
                           pure $ fromMaybe (unloadApp arity stk (CRef fc n)) ap
                   else pure $ unloadApp arity stk (CRef fc n)
  eval {vars} {free} rec env [] (CLam fc x sc)
      = do xn <- genName "lamv"
           sc' <- eval rec (env :< CRef fc xn) [] sc
           pure $ CLam fc x (refToLocal xn x sc')
  eval rec env (e :: stk) (CLam fc x sc) = eval rec (env :< e) stk sc
  eval {vars} {free} rec env stk (CLet fc x NotInline val sc)
      = do xn <- genName "letv"
           sc' <- eval rec (env :< CRef fc xn) [] sc
           val' <- eval rec env [] val
           pure (unload stk $ CLet fc x NotInline val' (refToLocal xn x sc'))
  eval {vars} {free} rec env stk (CLet fc x YesInline val sc)
      = do let u = used First sc
           if u < 1 -- TODO: Can make this <= as long as we know *all* inlinings
                    -- are guaranteed not to duplicate work. (We don't know
                    -- that yet).
              then do val' <- eval rec env [] val
                      eval rec (env :< val') stk sc
              else do xn <- genName "letv"
                      sc' <- eval rec (env :< CRef fc xn) stk sc
                      val' <- eval rec env [] val
                      pure (CLet fc x YesInline val' (refToLocal xn x sc'))
  eval rec env stk (CApp fc f@(CRef nfc n) args)
      = do -- If we don't know 'n' leave the arity alone, because it's
           -- a name from another module where the job is already done
           defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => do args' <- traverse (eval rec env []) args
                                pure (unload stk
                                          (CApp fc (CRef nfc n) args'))
           eval rec env (!(traverse (eval rec env []) args) ++ stk) f
  eval rec env stk (CApp fc f args)
      = eval rec env (!(traverse (eval rec env []) args) ++ stk) f
  eval rec env stk (CCon fc n ci t args)
      = pure $ unload stk $ CCon fc n ci t !(traverse (eval rec env []) args)
  eval rec env stk (COp fc p args)
      = pure $ unload stk $ COp fc p !(traverseVect (eval rec env []) args)
  eval rec env stk (CExtPrim fc p args)
      = pure $ unload stk $ CExtPrim fc p !(traverse (eval rec env []) args)
  eval rec env stk (CForce fc lr e)
      = case !(eval rec env [] e) of
             CDelay _ _ e' => eval rec [<] stk e'
             res => pure $ unload stk (CForce fc lr res) -- change this to preserve laziness semantics
  eval rec env stk (CDelay fc lr e)
      = pure $ unload stk (CDelay fc lr !(eval rec env [] e))
  eval rec env stk (CConCase fc sc alts def)
      = do sc' <- eval rec env [] sc
           let env' = update sc env sc'
           Nothing <- pickAlt rec env' stk sc' alts def | Just val => pure val
           def' <- traverseOpt (eval rec env' stk) def
           pure $ caseOfCase $ CConCase fc sc'
                     !(traverse (evalAlt fc rec env' stk) alts)
                     def'
    where
      updateLoc : {idx, vs : _} ->
                  (0 p : IsVar x idx (free ++ vs)) ->
                  EEnv free vs -> CExp free -> EEnv free vs
      updateLoc {vs = [<]} p env val = env
      updateLoc {vs = (xs :< x)} First (env :< e) val = env :< val
      updateLoc {vs = (xs :< y)} (Later p) (env :< e) val = updateLoc p env val :< e

      update : {vs : _} ->
               CExp (free ++ vs) -> EEnv free vs -> CExp free -> EEnv free vs
      update (CLocal _ p) env sc = updateLoc p env sc
      update _ env _ = env

  eval rec env stk (CConstCase fc sc alts def)
      = do sc' <- eval rec env [] sc
           Nothing <- pickConstAlt rec env stk sc' alts def | Just val => pure val
           def' <- traverseOpt (eval rec env stk) def
           pure $ caseOfCase $ CConstCase fc sc'
                         !(traverse (evalConstAlt rec env stk) alts)
                         def'
  eval rec env stk (CPrimVal fc c) = pure $ unload stk $ CPrimVal fc c
  eval rec env stk (CErased fc) = pure $ unload stk $ CErased fc
  eval rec env stk (CCrash fc str) = pure $ unload stk $ CCrash fc str

  extendLoc : {auto l : Ref LVar Int} ->
              FC -> EEnv free vars -> (args' : SnocList Name) ->
              Core (Bounds args', EEnv free (vars ++ args'))
  extendLoc fc env [<] = pure (None, env)
  extendLoc fc env (ns :< n)
      = do xn <- genName "cv"
           (bs', env') <- extendLoc fc env ns
           pure (Add n xn bs', env' :< CRef fc xn)

  evalAlt : {vars, free : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto l : Ref LVar Int} ->
            FC -> List Name -> EEnv free vars -> Stack free -> CConAlt (free ++ vars) ->
            Core (CConAlt free)
  evalAlt {free} {vars} fc rec env stk (MkConAlt n ci t args sc)
      = do (bs, env') <- extendLoc fc env args
           scEval <- eval rec env' stk
                          (rewrite appendAssociative free vars args in sc)
           pure $ MkConAlt n ci t args (refsToLocals bs scEval)

  evalConstAlt : {vars, free : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto l : Ref LVar Int} ->
                 List Name -> EEnv free vars -> Stack free -> CConstAlt (free ++ vars) ->
                 Core (CConstAlt free)
  evalConstAlt rec env stk (MkConstAlt c sc)
      = MkConstAlt c <$> eval rec env stk sc

  pickAlt : {vars, free : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto l : Ref LVar Int} ->
            List Name -> EEnv free vars -> Stack free ->
            CExp free -> List (CConAlt (free ++ vars)) ->
            Maybe (CExp (free ++ vars)) ->
            Core (Maybe (CExp free))
  pickAlt rec env stk (CCon fc n ci t args) [] def
      = traverseOpt (eval rec env stk) def
  pickAlt {vars} {free} rec env stk con@(CCon fc n ci t args) (MkConAlt n' _ t' args' sc :: alts) def
      =
        let args'' = cast args
        in if matches n t n' t'
           then case checkLengthMatch args'' args' of
                     Nothing => pure Nothing
                     Just m =>
                         do let env' : EEnv free (vars ++ args')
                                   = extend env args'' args' m
                            pure $ Just !(eval rec env' stk
                                    (rewrite appendAssociative free vars args' in
                                             sc))
           else pickAlt rec env stk con alts def
    where
      matches : Name -> Maybe Int -> Name -> Maybe Int -> Bool
      matches _ (Just t) _ (Just t') = t == t'
      matches n Nothing n' Nothing = n == n'
      matches _ _ _ _ = False
  pickAlt rec env stk _ _ _ = pure Nothing

  pickConstAlt : {vars, free : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto l : Ref LVar Int} ->
                 List Name -> EEnv free vars -> Stack free ->
                 CExp free -> List (CConstAlt (free ++ vars)) ->
                 Maybe (CExp (free ++ vars)) ->
                 Core (Maybe (CExp free))
  pickConstAlt rec env stk (CPrimVal fc c) [] def
      = traverseOpt (eval rec env stk) def
  pickConstAlt {vars} {free} rec env stk (CPrimVal fc c) (MkConstAlt c' sc :: alts) def
      = if c == c'
           then Just <$> eval rec env stk sc
           else pickConstAlt rec env stk (CPrimVal fc c) alts def
  pickConstAlt rec env stk _ _ _ = pure Nothing

-- Inlining may have messed with function arity (e.g. by adding lambdas to
-- the LHS to avoid needlessly making a closure) so fix them up here. This
-- needs to be right because typically back ends need to know whether a
-- name is under- or over-applied
fixArityTm : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             CExp vars -> List (CExp vars) -> Core (CExp vars)
fixArityTm (CRef fc n) args
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure (unload args (CRef fc n))
         let arity = case compexpr gdef of
                          Just def => getArity def
                          _ => 0
         pure $ expandToArity arity (CApp fc (CRef fc n) []) args
fixArityTm (CLam fc x sc) args
    = pure $ expandToArity Z (CLam fc x !(fixArityTm sc [])) args
fixArityTm (CLet fc x inl val sc) args
    = pure $ expandToArity Z
                 (CLet fc x inl !(fixArityTm val []) !(fixArityTm sc [])) args
fixArityTm outf@(CApp fc f@(CRef _ n) fargs) args
    = do defs <- get Ctxt
         -- If we don't know 'n' leave the arity alone, because it's
         -- a name from another module where the job is already done
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure (unload args outf)
         fixArityTm f (!(traverse (\tm => fixArityTm tm []) fargs) ++ args)
fixArityTm (CApp fc f fargs) args
    = fixArityTm f (!(traverse (\tm => fixArityTm tm []) fargs) ++ args)
fixArityTm (CCon fc n ci t args) []
    = pure $ CCon fc n ci t !(traverse (\tm => fixArityTm tm []) args)
fixArityTm (COp fc op args) []
    = pure $ COp fc op !(traverseArgs args)
  where
    traverseArgs : {vs : _} ->
                   Vect n (CExp vs) -> Core (Vect n (CExp vs))
    traverseArgs [] = pure []
    traverseArgs (a :: as) = pure $ !(fixArityTm a []) :: !(traverseArgs as)
fixArityTm (CExtPrim fc p args) []
    = pure $ CExtPrim fc p !(traverse (\tm => fixArityTm tm []) args)
fixArityTm (CForce fc lr tm) args
    = pure $ expandToArity Z (CForce fc lr !(fixArityTm tm [])) args
fixArityTm (CDelay fc lr tm) args
    = pure $ expandToArity Z (CDelay fc lr !(fixArityTm tm [])) args
fixArityTm (CConCase fc sc alts def) args
    = pure $ expandToArity Z
              (CConCase fc !(fixArityTm sc [])
                           !(traverse fixArityAlt alts)
                           !(traverseOpt (\tm => fixArityTm tm []) def)) args
  where
    fixArityAlt : CConAlt vars -> Core (CConAlt vars)
    fixArityAlt (MkConAlt n ci t a sc)
        = pure $ MkConAlt n ci t a !(fixArityTm sc [])
fixArityTm (CConstCase fc sc alts def) args
    = pure $ expandToArity Z
              (CConstCase fc !(fixArityTm sc [])
                             !(traverse fixArityConstAlt alts)
                             !(traverseOpt (\tm => fixArityTm tm []) def)) args
  where
    fixArityConstAlt : CConstAlt vars -> Core (CConstAlt vars)
    fixArityConstAlt (MkConstAlt c sc)
        = pure $ MkConstAlt c !(fixArityTm sc [])
fixArityTm t [] = pure t
fixArityTm t args = pure $ expandToArity Z t args

export
fixArityExp : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              CExp vars -> Core (CExp vars)
fixArityExp tm = fixArityTm tm []

fixArity : {auto c : Ref Ctxt Defs} ->
           CDef -> Core CDef
fixArity (MkFun args exp) = pure $ MkFun args !(fixArityTm exp [])
fixArity (MkError exp) = pure $ MkError !(fixArityTm exp [])
fixArity d = pure d

-- TODO: get rid of this `done` by making the return `args'` runtime irrelevant?
getLams : {done : _} -> SizeOf done ->
          Int -> SubstCEnv done args -> CExp (args ++ done) ->
          (args' ** (SizeOf args', SubstCEnv args' args, CExp (args ++ args')))
getLams {done} d i env (CLam fc x sc)
    = getLams {done = done :< x} (suc d) (i + 1) (env :< CRef fc (MN "ext" i)) sc
getLams {done} d i env sc = (done ** (d, env, sc))

mkBounds : (xs : _) -> Bounds xs
mkBounds [<] = None
mkBounds (xs :< x) = Add x x (mkBounds xs)

getNewArgs : {done : _} ->
             SubstCEnv done args -> SnocList Name
getNewArgs [<] = [<]
getNewArgs (xs :< CRef _ n) = getNewArgs xs :< n
getNewArgs {done = xs :< x} (sub :< _) = getNewArgs sub :< x

-- Move any lambdas in the body of the definition into the lhs list of vars.
-- Annoyingly, the indices will need fixing up because the order in the top
-- level definition goes left to right (i.e. first argument has lowest index,
-- not the highest, as you'd expect if they were all lambdas).
mergeLambdas : (args : SnocList Name) -> CExp args -> (args' ** CExp args')
mergeLambdas args (CLam fc x sc)
    = let (args' ** (s, env, exp')) = getLams zero 0 [<] (CLam fc x sc)
          expNs = substs s env exp'
          newArgs = reverse $ getNewArgs env
          expLocs = mkLocals (mkSizeOf args) {vars = [<]} (mkBounds newArgs)
                             (rewrite appendLinLeftNeutral args in expNs) in
          (_ ** expLocs)
mergeLambdas args exp = (args ** exp)

||| Inline all inlinable functions into the given expression.
||| @ n the function name
||| @ exp the body of the function
doEval : {args : _} ->
         {auto c : Ref Ctxt Defs} ->
         (n : Name) -> (exp : CExp args) -> Core (CExp args)
doEval n exp
    = do l <- newRef LVar (the Int 0)
         log "compiler.inline.eval" 10 (show n ++ ": " ++ show exp)
         exp' <- logDepth $ eval [] [<] [] exp
         log "compiler.inline.eval" 10 ("Inlined: " ++ show exp')
         pure exp'

inline : {auto c : Ref Ctxt Defs} ->
         Name -> CDef -> Core CDef
inline n (MkFun args def)
    = pure $ MkFun args !(doEval n def)
inline n d = pure d

-- merge lambdas from expression into top level arguments
mergeLam : {auto c : Ref Ctxt Defs} ->
           CDef -> Core CDef
mergeLam (MkFun args def)
    = do let (args' ** exp') = mergeLambdas args def
         pure $ MkFun args' exp'
mergeLam d = pure d

mutual
  addRefs : NameMap Bool -> CExp vars -> NameMap Bool
  addRefs ds (CRef _ n) = insert n False ds
  addRefs ds (CLam _ _ sc) = addRefs ds sc
  addRefs ds (CLet _ _ _ val sc) = addRefs (addRefs ds val) sc
  addRefs ds (CApp _ f args) = addRefsArgs (addRefs ds f) args
  addRefs ds (CCon _ n _ _ args) = addRefsArgs (insert n False ds) args
  addRefs ds (COp _ _ args) = addRefsArgs ds (toList args)
  addRefs ds (CExtPrim _ _ args) = addRefsArgs ds args
  addRefs ds (CForce _ _ e) = addRefs ds e
  addRefs ds (CDelay _ _ e) = addRefs ds e
  addRefs ds (CConCase _ sc alts def)
      = let ds' = maybe ds (addRefs ds) def in
            addRefsConAlts (addRefs ds' sc) alts
  addRefs ds (CConstCase _ sc alts def)
      = let ds' = maybe ds (addRefs ds) def in
            addRefsConstAlts (addRefs ds' sc) alts
  addRefs ds tm = ds

  addRefsArgs : NameMap Bool -> List (CExp vars) -> NameMap Bool
  addRefsArgs ds [] = ds
  addRefsArgs ds (a :: as) = addRefsArgs (addRefs ds a) as

  addRefsConAlts : NameMap Bool -> List (CConAlt vars) -> NameMap Bool
  addRefsConAlts ds [] = ds
  addRefsConAlts ds (MkConAlt n _ _ _ sc :: rest)
      = addRefsConAlts (addRefs (insert n False ds) sc) rest

  addRefsConstAlts : NameMap Bool -> List (CConstAlt vars) -> NameMap Bool
  addRefsConstAlts ds [] = ds
  addRefsConstAlts ds (MkConstAlt _ sc :: rest)
      = addRefsConstAlts (addRefs ds sc) rest

getRefs : CDef -> NameMap Bool
getRefs (MkFun args exp) = addRefs empty exp
getRefs _ = empty

export
inlineDef : {auto c : Ref Ctxt Defs} ->
            Name -> Core ()
inlineDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr = compexpr def              | Nothing => pure ()
         setCompiled n !(inline n cexpr)

-- Update the names a function refers to at runtime based on the transformation
-- results (saves generating code unnecessarily).
updateCallGraph : {auto c : Ref Ctxt Defs} ->
                  Name -> Core ()
updateCallGraph n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         let refs = getRefs cexpr
         ignore $ addDef n ({ refersToRuntimeM := Just refs } def)

export
fixArityDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
fixArityDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         setCompiled n !(fixArity cexpr)

export
mergeLamDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
mergeLamDef n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         let PMDef pi _ _ _ _ = definition def
              | _ => pure ()
         if not (isNil (incrementalCGs !getSession)) &&
                externalDecl pi -- better keep it at arity 0
            then pure ()
            else do let Just cexpr =  compexpr def
                             | Nothing => pure ()
                    setCompiled n !(mergeLam cexpr)

export
addArityHash : {auto c : Ref Ctxt Defs} ->
               Name -> Core ()
addArityHash n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure ()
         let Just cexpr =  compexpr def             | Nothing => pure ()
         let MkFun args _ = cexpr                   | _ => pure ()
         case collapseDefault $ visibility def of
              Private => pure ()
              _ => addHash (n, length args)

export
compileAndInlineAll : {auto c : Ref Ctxt Defs} ->
                      Core ()
compileAndInlineAll
    = do defs <- get Ctxt
         let ns = keys (toIR defs)
         cns <- filterM nonErased ns

         traverse_ (logDepthWrap compileDef) cns
         traverse_ (logDepthWrap rewriteIdentityFlag) cns
         transform 3 cns -- number of rounds to run transformations.
                         -- This seems to be the point where not much useful
                         -- happens any more.
         traverse_ (logDepthWrap updateCallGraph) cns
         -- in incremental mode, add the arity of the definitions to the hash,
         -- because if these change we need to recompile dependencies
         -- accordingly
         unless (isNil (incrementalCGs !getSession)) $
           traverse_ (logDepthWrap addArityHash) cns
  where
    transform : Nat -> List Name -> Core ()
    transform Z cns = pure ()
    transform (S k) cns
        = do traverse_ inlineDef cns
             traverse_ mergeLamDef cns
             traverse_ caseLamDef cns
             traverse_ fixArityDef cns
             traverse_ inlineHeuristics cns
             traverse_ constantFold cns
             traverse_ setIdentity cns
             transform k cns

    nonErased : Name -> Core Bool
    nonErased n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (multiplicity gdef /= erased)
