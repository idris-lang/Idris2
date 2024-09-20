module TTImp.ProcessDef

import Core.Case.CaseBuilder
import Core.Case.CaseTree
import Core.Case.CaseTree.Pretty
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Coverage
import Core.Env
import Core.Hash
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Termination
import Core.Termination.CallGraph
import Core.Transform
import Core.Value
import Core.UnifyState

import Idris.REPL.Opts
import Idris.Syntax
import Idris.Pretty.Annotations

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Impossible
import TTImp.PartialEval
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.ProcessType
import TTImp.Unelab
import TTImp.WithClause

import Data.Either
import Data.List
import Data.String
import Data.Maybe
import Libraries.Data.NameMap
import Libraries.Data.WithDefault
import Libraries.Text.PrettyPrint.Prettyprinter

%default covering

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

  -- NPrimVal is apart from NDCon, NTCon, NBind, and NType
  mismatchNF defs (NPrimVal _ _) (NDCon _ _ _ _ _) = pure True
  mismatchNF defs (NDCon _ _ _ _ _) (NPrimVal _ _) = pure True
  mismatchNF defs (NPrimVal _ _) (NBind _ _ _ _) = pure True
  mismatchNF defs (NBind _ _ _ _) (NPrimVal _ _) = pure True
  mismatchNF defs (NPrimVal _ _) (NTCon _ _ _ _ _) = pure True
  mismatchNF defs (NTCon _ _ _ _ _) (NPrimVal _ _) = pure True
  mismatchNF defs (NPrimVal _ _) (NType _ _) = pure True
  mismatchNF defs (NType _ _) (NPrimVal _ _) = pure True

-- NTCon is apart from NBind, and NType
  mismatchNF defs (NTCon _ _ _ _ _) (NBind _ _ _ _) = pure True
  mismatchNF defs (NBind _ _ _ _) (NTCon _ _ _ _ _) = pure True
  mismatchNF defs (NTCon _ _ _ _ _) (NType _ _) = pure True
  mismatchNF defs (NType _ _) (NTCon _ _ _ _ _) = pure True

-- NBind is apart from NType
  mismatchNF defs (NBind _ _ _ _) (NType _ _) = pure True
  mismatchNF defs (NType _ _) (NBind _ _ _ _) = pure True

  mismatchNF _ _ _ = pure False

  mismatch : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Defs -> (Closure vars, Closure vars) -> Core Bool
  mismatch defs (x, y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
export
impossibleOK : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
impossibleOK defs (NTCon _ xn xt xa xargs) (NTCon _ yn yt ya yargs)
    = if xn /= yn
         then pure True
         else anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
-- If it's a data constructor, any mismatch will do
impossibleOK defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
impossibleOK defs (NPrimVal _ x) (NPrimVal _ y) = pure (x /= y)

-- NPrimVal is apart from NDCon, NTCon, NBind, and NType
impossibleOK defs (NPrimVal _ _) (NDCon _ _ _ _ _) = pure True
impossibleOK defs (NDCon _ _ _ _ _) (NPrimVal _ _) = pure True
impossibleOK defs (NPrimVal _ _) (NBind _ _ _ _) = pure True
impossibleOK defs (NBind _ _ _ _) (NPrimVal _ _) = pure True
impossibleOK defs (NPrimVal _ _) (NTCon _ _ _ _ _) = pure True
impossibleOK defs (NTCon _ _ _ _ _) (NPrimVal _ _) = pure True
impossibleOK defs (NPrimVal _ _) (NType _ _) = pure True
impossibleOK defs (NType _ _) (NPrimVal _ _) = pure True

-- NTCon is apart from NBind, and NType
impossibleOK defs (NTCon _ _ _ _ _) (NBind _ _ _ _) = pure True
impossibleOK defs (NBind _ _ _ _) (NTCon _ _ _ _ _) = pure True
impossibleOK defs (NTCon _ _ _ _ _) (NType _ _) = pure True
impossibleOK defs (NType _ _) (NTCon _ _ _ _ _) = pure True

-- NBind is apart from NType
impossibleOK defs (NBind _ _ _ _) (NType _ _) = pure True
impossibleOK defs (NType _ _) (NBind _ _ _ _) = pure True

impossibleOK defs x y = pure False

export
impossibleErrOK : {auto c : Ref Ctxt Defs} ->
                  Defs -> Error -> Core Bool
impossibleErrOK defs (CantConvert fc gam env l r)
    = do let defs = { gamma := gam } defs
         impossibleOK defs !(nf defs env l)
                           !(nf defs env r)
impossibleErrOK defs (CantSolveEq fc gam env l r)
    = do let defs = { gamma := gam } defs
         impossibleOK defs !(nf defs env l)
                           !(nf defs env r)
impossibleErrOK defs (BadDotPattern _ _ ErasedArg _ _) = pure True
impossibleErrOK defs (CyclicMeta _ _ _ _) = pure True
impossibleErrOK defs (AllFailed errs)
    = anyM (impossibleErrOK defs) (map snd errs)
impossibleErrOK defs (WhenUnifying _ _ _ _ _ err)
    = impossibleErrOK defs err
impossibleErrOK defs _ = pure False

-- If it's a clause we've generated, see if the error is recoverable. That
-- is, if we have a concrete thing, and we're expecting the same concrete
-- thing, or a function of something, then we might have a match.
export
recoverable : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              Defs -> NF vars -> NF vars -> Core Bool
-- Unlike the above, any mismatch will do

-- TYPE CONSTRUCTORS
recoverable defs (NTCon _ xn xt xa xargs) (NTCon _ yn yt ya yargs)
    = if xn /= yn
         then pure False
         else pure $ not !(anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs))
-- Type constructor vs. primitive type
recoverable defs (NTCon _ _ _ _ _) (NPrimVal _ _) = pure False
recoverable defs (NPrimVal _ _) (NTCon _ _ _ _ _) = pure False
-- Type constructor vs. type
recoverable defs (NTCon _ _ _ _ _) (NType _ _) = pure False
recoverable defs (NType _ _) (NTCon _ _ _ _ _) = pure False
-- Type constructor vs. binder
recoverable defs (NTCon _ _ _ _ _) (NBind _ _ _ _) = pure False
recoverable defs (NBind _ _ _ _) (NTCon _ _ _ _ _) = pure False

recoverable defs (NTCon _ _ _ _ _) _ = pure True
recoverable defs _ (NTCon _ _ _ _ _) = pure True

-- DATA CONSTRUCTORS
recoverable defs (NDCon _ _ xt _ xargs) (NDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure False
         else pure $ not !(anyMScoped (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs))
-- Data constructor vs. primitive constant
recoverable defs (NDCon _ _ _ _ _) (NPrimVal _ _) = pure False
recoverable defs (NPrimVal _ _) (NDCon _ _ _ _ _) = pure False

recoverable defs (NDCon _ _ _ _ _) _ = pure True
recoverable defs _ (NDCon _ _ _ _ _) = pure True

-- FUNCTION CALLS
recoverable defs (NApp _ (NRef _ f) fargs) (NApp _ (NRef _ g) gargs)
    = pure True -- both functions; recoverable

-- PRIMITIVES
recoverable defs (NPrimVal _ x) (NPrimVal _ y) = pure (x == y)
-- primitive vs. binder
recoverable defs (NPrimVal _ _) (NBind _ _ _ _) = pure False
recoverable defs (NBind _ _ _ _) (NPrimVal _ _) = pure False

-- OTHERWISE: no
recoverable defs x y = pure False

export
recoverableErr : {auto c : Ref Ctxt Defs} ->
                 Defs -> Error -> Core Bool
recoverableErr defs (CantConvert fc gam env l r)
  = do let defs = { gamma := gam } defs
       l <- nf defs env l
       r <- nf defs env r
       log "coverage.recover" 10 $ unlines
         [ "Recovering from CantConvert?"
         , "Checking:"
         , "  " ++ show l
         , "  " ++ show r
         ]
       recoverable defs l r

recoverableErr defs (CantSolveEq fc gam env l r)
  = do let defs = { gamma := gam } defs
       recoverable defs !(nf defs env l)
                        !(nf defs env r)
recoverableErr defs (BadDotPattern _ _ ErasedArg _ _) = pure True
recoverableErr defs (CyclicMeta _ _ _ _) = pure False
-- Don't mark a case as impossible because we can't see the constructor.
recoverableErr defs (InvisibleName _ _ _) = pure True
recoverableErr defs (AllFailed errs)
    = anyM (recoverableErr defs) (map snd errs)
recoverableErr defs (WhenUnifying _ _ _ _ _ err)
    = recoverableErr defs err
recoverableErr defs _ = pure False

-- Given a type checked LHS and its type, return the environment in which we
-- should check the RHS, the LHS and its type in that environment,
-- and a function which turns a checked RHS into a
-- pattern clause
-- The 'Thin' proof contains a proof that refers to the *inner* environment,
-- so all the outer things are marked as 'Drop'
extendEnv : {vars : _} ->
            Env Term vars -> Thin inner vars ->
            NestedNames vars ->
            Term vars -> Term vars ->
            Core (vars' **
                    (Thin inner vars',
                     Env Term vars', NestedNames vars',
                     Term vars', Term vars'))
extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy _ _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy _ _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n (PVTy _ _ _) tysc) | (Just Refl)
      = extendEnv (PVar fc c pi tmty :: env) (Drop p) (weaken nest) sc tysc
extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet _ _ _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet _ _ _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  -- PLet on the left becomes Let on the right, to give it computational force
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n (PLet _ _ _ _) tysc) | (Just Refl)
      = extendEnv (Let fc c tmval tmty :: env) (Drop p) (weaken nest) sc tysc
extendEnv env p nest tm ty
      = pure (_ ** (p, env, nest, tm, ty))

-- Find names which are applied to a function in a Rig1/Rig0 position,
-- so that we know how they should be bound on the right hand side of the
-- pattern.
-- 'bound' counts the number of variables locally bound; these are the
-- only ones we're checking linearity of (we may be shadowing names if this
-- is a local definition, so we need to leave the earlier ones alone)
findLinear : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Bool -> Nat -> RigCount -> Term vars ->
             Core (List (Name, RigCount))
findLinear top bound rig (Bind fc n b sc)
    = findLinear top (S bound) rig sc
findLinear top bound rig (As fc _ _ p)
    = findLinear top bound rig p
findLinear top bound rig tm
    = case getFnArgs tm of
           (Ref _ _ n, []) => pure []
           (Ref _ nt n, args)
              => do defs <- get Ctxt
                    Just nty <- lookupTyExact n (gamma defs)
                         | Nothing => pure []
                    findLinArg (accessible nt rig) !(nf defs [] nty) args
           _ => pure []
    where
      accessible : NameType -> RigCount -> RigCount
      accessible Func r = if top then r else erased
      accessible _ r = r

      findLinArg : {vars : _} ->
                   RigCount -> NF [<] -> List (Term vars) ->
                   Core (List (Name, RigCount))
      findLinArg rig ty@(NBind _ _ (Pi _ c _ _) _) (As fc u a p :: as)
          = if isLinear c
               then case u of
                         UseLeft => findLinArg rig ty (p :: as)
                         UseRight => findLinArg rig ty (a :: as)
               else pure $ !(findLinArg rig ty [a]) ++ !(findLinArg rig ty (p :: as))
      findLinArg rig (NBind _ x (Pi _ c _ _) sc) (Local {name=a} fc _ idx prf :: as)
          = do defs <- get Ctxt
               let a = nameAt prf
               if idx < bound
                 then do sc' <- sc defs (toClosure defaultOpts [] (Ref fc Bound x))
                         pure $ (a, rigMult c rig) ::
                                    !(findLinArg rig sc' as)
                 else do sc' <- sc defs (toClosure defaultOpts [] (Ref fc Bound x))
                         findLinArg rig sc' as
      findLinArg rig (NBind fc x (Pi _ c _ _) sc) (a :: as)
          = do defs <- get Ctxt
               pure $ !(findLinear False bound (c |*| rig) a) ++
                      !(findLinArg rig !(sc defs (toClosure defaultOpts [] (Ref fc Bound x))) as)
      findLinArg rig ty (a :: as)
          = pure $ !(findLinear False bound rig a) ++ !(findLinArg rig ty as)
      findLinArg _ _ [] = pure []

setLinear : List (Name, RigCount) -> Term vars -> Term vars
setLinear vs (Bind fc x b@(PVar _ _ _ _) sc)
    = case lookup x vs of
           Just c' => Bind fc x (setMultiplicity b c') (setLinear vs sc)
           _ => Bind fc x b (setLinear vs sc)
setLinear vs (Bind fc x b@(PVTy _ _ _) sc)
    = case lookup x vs of
           Just c' => Bind fc x (setMultiplicity b c') (setLinear vs sc)
           _ => Bind fc x b (setLinear vs sc)
setLinear vs tm = tm

-- Combining multiplicities on LHS:
-- Rig1 + Rig1/W not valid, since it means we have repeated use of name
-- Rig0 + RigW = RigW
-- Rig0 + Rig1 = Rig1
combineLinear : FC -> List (Name, RigCount) ->
                Core (List (Name, RigCount))
combineLinear loc [] = pure []
combineLinear loc ((n, count) :: cs)
    = case lookupAll n cs of
           [] => pure $ (n, count) :: !(combineLinear loc cs)
           counts => do count' <- combineAll count counts
                        pure $ (n, count') ::
                               !(combineLinear loc (filter notN cs))
  where
    notN : (Name, RigCount) -> Bool
    notN (n', _) = n /= n'

    lookupAll : Name -> List (Name, RigCount) -> List RigCount
    lookupAll n [] = []
    lookupAll n ((n', c) :: cs)
       = if n == n' then c :: lookupAll n cs else lookupAll n cs

    -- Those combine rules are obtuse enough that they are worth investigating
    combine : RigCount -> RigCount -> Core RigCount
    combine l r = if l |+| r == top && not (isErased $ l `glb` r) && (l `glb` r) /= top
                     then throw (LinearUsed loc 2 n)
                     -- if everything is fine, return the linearity that has the
                     -- highest bound
                     else pure (l `lub` r)

    combineAll : RigCount -> List RigCount -> Core RigCount
    combineAll c [] = pure c
    combineAll c (c' :: cs)
        = do newc <- combine c c'
             combineAll newc cs

export -- also used by Transforms
checkLHS : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           Bool -> -- in transform
           (mult : RigCount) ->
           Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
           FC -> RawImp ->
           Core (RawImp, -- checked LHS with implicits added
                 (vars' ** (Thin vars vars',
                           Env Term vars', NestedNames vars',
                           Term vars', Term vars')))
checkLHS {vars} trans mult n opts nest env fc lhs_in
    = do defs <- get Ctxt
         logRaw "declare.def.lhs" 30 "Raw LHS: " lhs_in
         lhs_raw <- if trans
                       then pure lhs_in
                       else lhsInCurrentNS nest lhs_in
         logRaw "declare.def.lhs" 30 "Raw LHS in current NS: " lhs_raw

         autoimp <- isUnboundImplicits
         setUnboundImplicits True
         (_, lhs_bound) <- bindNames False lhs_raw
         setUnboundImplicits autoimp
         logRaw "declare.def.lhs" 30 "Raw LHS with implicits bound" lhs_bound

         lhs <- if trans
                   then pure lhs_bound
                   else implicitsAs n defs (toList vars) lhs_bound

         logC "declare.def.lhs" 5 $ do pure $ "Checking LHS of " ++ show !(getFullName (Resolved n))
-- todo: add Pretty RawImp instance
--         logC "declare.def.lhs" 5 $ do pure $ show $ indent {ann = ()} 2 $ pretty lhs
         log "declare.def.lhs" 10 $ show lhs
         logEnv "declare.def.lhs" 5 "In env" env
         let lhsMode = if trans
                          then InTransform
                          else InLHS mult
         (lhstm, lhstyg) <-
             wrapErrorC opts (InLHS fc !(getFullName (Resolved n))) $
                     elabTerm n lhsMode opts nest env
                                (IBindHere fc PATTERN lhs) Nothing
         logTerm "declare.def.lhs" 5 "Checked LHS term" lhstm
         lhsty <- getTerm lhstyg

         defs <- get Ctxt
         let lhsenv = letToLam env
         -- we used to fully normalise the LHS, to make sure fromInteger
         -- patterns were allowed, but now they're fully normalised anyway
         -- so we only need to do the holes. If there's a lot of type level
         -- computation, this is a huge saving!
         lhstm <- normaliseHoles defs lhsenv lhstm
         lhsty <- normaliseHoles defs env lhsty
         linvars_in <- findLinear True 0 linear lhstm
         logTerm "declare.def.lhs" 10 "Checked LHS term after normalise" lhstm
         log "declare.def.lhs" 5 $ "Linearity of names in " ++ show n ++ ": " ++
                 show linvars_in

         linvars <- combineLinear fc linvars_in
         let lhstm_lin = setLinear linvars lhstm
         let lhsty_lin = setLinear linvars lhsty

         logTerm "declare.def.lhs" 3 "LHS term" lhstm_lin
         logTerm "declare.def.lhs" 5 "LHS type" lhsty_lin
         setHoleLHS (bindEnv fc env lhstm_lin)

         ext <- extendEnv env Refl nest lhstm_lin lhsty_lin
         pure (lhs, ext)

-- Return whether any of the pattern variables are in a trivially empty
-- type, where trivally empty means one of:
--  * No constructors
--  * Every constructor of the family has a return type which conflicts with
--    the given constructor's type
hasEmptyPat : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Defs -> Env Term vars -> Term vars -> Core Bool
hasEmptyPat defs env (Bind fc x b sc)
   = pure $ !(isEmpty defs env !(nf defs env (binderType b)))
            || !(hasEmptyPat defs (b :: env) sc)
hasEmptyPat defs env _ = pure False

-- For checking with blocks as nested names
applyEnv : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Env Term vars -> Name ->
           Core (Name, (Maybe Name, List (Var vars), FC -> NameType -> Term vars))
applyEnv env withname
    = do n' <- resolveName withname
         pure (withname, (Just withname, reverse (allVarsNoLet env),
                  \fc, nt => applyTo fc
                         (Ref fc nt (Resolved n')) env))

-- Check a pattern clause, returning the component of the 'Case' expression it
-- represents, or Nothing if it's an impossible clause
export
checkClause : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              (mult : RigCount) -> (vis : Visibility) ->
              (totreq : TotalReq) -> (hashit : Bool) ->
              Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
              ImpClause -> Core (Either RawImp Clause)
checkClause mult vis totreq hashit n opts nest env (ImpossibleClause fc lhs)
    = do lhs_raw <- lhsInCurrentNS nest lhs
         handleUnify
           (do autoimp <- isUnboundImplicits
               setUnboundImplicits True
               (_, lhs) <- bindNames False lhs_raw
               setUnboundImplicits autoimp

               log "declare.def.clause.impossible" 5 $ "Checking " ++ show lhs
               logEnv "declare.def.clause.impossible" 5 "In env" env
               (lhstm, lhstyg) <-
                           elabTerm n (InLHS mult) opts nest env
                                      (IBindHere fc PATTERN lhs) Nothing
               defs <- get Ctxt
               lhs <- normaliseHoles defs env lhstm
               if !(hasEmptyPat defs env lhs)
                  then pure (Left lhs_raw)
                  else throw (ValidCase fc env (Left lhs)))
           (\err =>
              case err of
                   ValidCase _ _ _ => throw err
                   _ => do defs <- get Ctxt
                           if !(impossibleErrOK defs err)
                              then pure (Left lhs_raw)
                              else throw (ValidCase fc env (Right err)))
checkClause {vars} mult vis totreq hashit n opts nest env (PatClause fc lhs_in rhs)
    = do (_, (vars'  ** (sub', env', nest', lhstm', lhsty'))) <-
             checkLHS False mult n opts nest env fc lhs_in
         let rhsMode = if isErased mult then InType else InExpr
         log "declare.def.clause" 5 $ "Checking RHS " ++ show rhs
         logEnv "declare.def.clause" 5 "In env" env'

         rhstm <- logTime 3 ("Check RHS " ++ show fc) $
                    wrapErrorC opts (InRHS fc !(getFullName (Resolved n))) $
                       checkTermSub n rhsMode opts nest' env' env sub' rhs (gnf env' lhsty')
         clearHoleLHS

         logTerm "declare.def.clause" 3 "RHS term" rhstm
         when hashit $
           do addHashWithNames lhstm'
              addHashWithNames rhstm
              log "module.hash" 15 "Adding hash for def."

         -- If the rhs is a hole, record the lhs in the metadata because we
         -- might want to split it interactively
         case rhstm of
              Meta _ _ _ _ =>
                 addLHS (getFC lhs_in) (length env) env' lhstm'
              _ => pure ()

         pure (Right (MkClause env' lhstm' rhstm))
-- TODO: (to decide) With is complicated. Move this into its own module?
checkClause {vars} mult vis totreq hashit n opts nest env
    (WithClause ifc lhs_in rig wval_raw mprf flags cs)
    = do (lhs, (vars'  ** (sub', env', nest', lhspat, reqty))) <-
             checkLHS False mult n opts nest env ifc lhs_in
         let wmode
               = if isErased mult || isErased rig then InType else InExpr

         (wval, gwvalTy) <- wrapErrorC opts (InRHS ifc !(getFullName (Resolved n))) $
                elabTermSub n wmode opts nest' env' env sub' wval_raw Nothing
         clearHoleLHS

         logTerm "declare.def.clause.with" 5 "With value (at quantity \{show rig})" wval
         logTerm "declare.def.clause.with" 3 "Required type" reqty
         wvalTy <- getTerm gwvalTy
         defs <- get Ctxt
         wval <- normaliseHoles defs env' wval
         wvalTy <- normaliseHoles defs env' wvalTy

         let (wevars ** withSub) = keepOldEnv sub' (snd (findSubEnv env' wval))
         logTerm "declare.def.clause.with" 5 "With value type" wvalTy
         log "declare.def.clause.with" 5 $ "Using vars " ++ show wevars

         let Just wval = shrink wval withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #1")
         let Just wvalTy = shrink wvalTy withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #2")
         -- Should the env be normalised too? If the following 'impossible'
         -- error is ever thrown, that might be the cause!
         let Just wvalEnv = shrinkEnv env' withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #3")

         -- Abstracting over 'wval' in the scope of bNotReq in order
         -- to get the 'magic with' behaviour
         (wargs ** (scenv, var, binder)) <- bindWithArgs rig wvalTy ((,wval) <$> mprf) wvalEnv

         let bnr = bindNotReq vfc 0 env' withSub [] reqty
         let notreqns = fst bnr
         let notreqty = snd bnr

         rdefs <- if Syntactic `elem` flags
                     then clearDefs defs
                     else pure defs
         wtyScope <- replace rdefs scenv !(nf rdefs scenv (weakenNs (mkSizeOf wargs) wval))
                            var
                            !(nf rdefs scenv
                                 (weakenNs (mkSizeOf wargs) notreqty))
         let bNotReq = binder wtyScope

         -- The environment has some implicit and some explcit args, potentially,
         -- which is inconvenient since we have to know which is which when
         -- elaborating the application of the rhs function. So it's easier
         -- if we just make them all explicit - this type isn't visible to
         -- users anyway!
         let env' = mkExplicit env'

         let Just (reqns, envns, wtype) = bindReq vfc env' withSub [] bNotReq
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #4")

         -- list of argument names - 'Just' means we need to match the name
         -- in the with clauses to find out what the pattern should be.
         -- 'Nothing' means it's the with pattern (so wargn)
         let wargNames
                 = map Just reqns ++
                   Nothing :: map Just notreqns

         logTerm "declare.def.clause.with" 3 "With function type" wtype
         log "declare.def.clause.with" 5 $ "Argument names " ++ show wargNames

         wname <- genWithName !(prettyName !(toFullNames (Resolved n)))
         widx <- addDef wname ({flags $= (SetTotal totreq ::)}
                                    (newDef vfc wname (if isErased mult then erased else top)
                                      vars wtype (specified vis) None))

         let toWarg : Maybe (PiInfo RawImp, Name) -> List (Maybe Name, RawImp)
               := flip maybe (\pn => [(Nothing, IVar vfc (snd pn))]) $
                    (Nothing, wval_raw) ::
                    case mprf of
                      Nothing => []
                      Just _  =>
                       let fc = emptyFC in
                       let refl = IVar fc (NS builtinNS (UN $ Basic "Refl")) in
                       [(map snd mprf, INamedApp fc refl (UN $ Basic "x") wval_raw)]

         let rhs_in = gapply (IVar vfc wname)
                    $ map (\ nm => (Nothing, IVar vfc nm)) envns
                   ++ concatMap toWarg wargNames

         log "declare.def.clause.with" 3 $ "Applying to with argument " ++ show rhs_in
         rhs <- wrapErrorC opts (InRHS ifc !(getFullName (Resolved n))) $
             checkTermSub n wmode opts nest' env' env sub' rhs_in
                          (gnf env' reqty)

         -- Generate new clauses by rewriting the matched arguments
         cs' <- traverse (mkClauseWith 1 wname wargNames lhs) cs
         log "declare.def.clause.with" 3 $ "With clauses: " ++ show cs'

         -- Elaborate the new definition here
         nestname <- applyEnv env wname
         let nest'' = { names $= (nestname ::) } nest

         let wdef = IDef ifc wname cs'
         processDecl [] nest'' env wdef

         pure (Right (MkClause env' lhspat rhs))
  where
    vfc : FC
    vfc = virtualiseFC ifc

    mkExplicit : forall vs . Env Term vs -> Env Term vs
    mkExplicit [] = []
    mkExplicit (Pi fc c _ ty :: env) = Pi fc c Explicit ty :: mkExplicit env
    mkExplicit (b :: env) = b :: mkExplicit env

    bindWithArgs :
       (rig : RigCount) -> (wvalTy : Term xs) -> Maybe ((RigCount, Name), Term xs) ->
       (wvalEnv : Env Term xs) ->
       Core (ext : SnocList Name
         ** ( Env Term (xs ++ ext)
            , Term (xs ++ ext)
            , (Term (xs ++ ext) -> Term xs)
            ))
    bindWithArgs {xs} rig wvalTy Nothing wvalEnv =
      let wargn : Name
          wargn = MN "warg" 0
          wargs : SnocList Name
          wargs = (wargn :%: [<])

          scenv : Env Term (xs ++ wargs)
                := Pi vfc top Explicit wvalTy :: wvalEnv

          var : Term (xs ++ wargs)
              := Local vfc (Just False) Z First

          binder : Term (xs ++ wargs) -> Term xs
                 := Bind vfc wargn (Pi vfc rig Explicit wvalTy)

      in pure (wargs ** (scenv, var, binder))

    bindWithArgs {xs} rig wvalTy (Just ((rigPrf, name), wval)) wvalEnv = do
      defs <- get Ctxt

      let eqName = NS builtinNS (UN $ Basic "Equal")
      Just (TCon t ar _ _ _ _ _ _) <- lookupDefExact eqName (gamma defs)
        | _ => throw (InternalError "Cannot find builtin Equal")
      let eqTyCon = Ref vfc (TyCon t ar) !(toResolvedNames eqName)

      let wargn : Name
          wargn = MN "warg" 0
          wargs : SnocList Name
          wargs = (name :%: wargn :%: [<])

          wvalTy' := weaken wvalTy
          eqTy : Term (xs :< MN "warg" 0)
               := apply vfc eqTyCon
                           [ wvalTy'
                           , wvalTy'
                           , weaken wval
                           , Local vfc (Just False) Z First
                           ]

          scenv : Env Term (xs ++ wargs)
                := Pi vfc top Implicit eqTy
                :: Pi vfc top Explicit wvalTy
                :: wvalEnv

          var : Term (xs ++ wargs)
              := Local vfc (Just False) (S Z) (Later First)

          binder : Term (xs ++ wargs) -> Term xs
                 := \ t => Bind vfc wargn (Pi vfc rig Explicit wvalTy)
                         $ Bind vfc name  (Pi vfc rigPrf Implicit eqTy) t

      pure (wargs ** (scenv, var, binder))

    -- If it's 'Keep/Refl' in 'outprf', that means it was in the outer
    -- environment so we need to keep it in the same place in the 'with'
    -- function. Hence, turn it to Keep whatever
    keepOldEnv : {0 outer : _} -> {vs : _} ->
                 (outprf : Thin outer vs) -> Thin vs' vs ->
                 (vs'' : SnocList Name ** Thin vs'' vs)
    keepOldEnv {vs} Refl p = (vs ** Refl)
    keepOldEnv {vs} p Refl = (vs ** Refl)
    keepOldEnv (Drop p) (Drop p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** Drop rest)
    keepOldEnv (Drop p) (Keep p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** Keep rest)
    keepOldEnv (Keep p) (Drop p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** Keep rest)
    keepOldEnv (Keep p) (Keep p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** Keep rest)

    -- Rewrite the clauses in the block to use an updated LHS.
    -- 'drop' is the number of additional with arguments we expect
    -- (i.e. the things to drop from the end before matching LHSs)
    mkClauseWith : (drop : Nat) -> Name ->
                   List (Maybe (PiInfo RawImp, Name)) ->
                   RawImp -> ImpClause ->
                   Core ImpClause
    mkClauseWith drop wname wargnames lhs (PatClause ploc patlhs rhs)
        = do log "declare.def.clause.with" 20 "PatClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             newrhs <- withRHS ploc drop wname wargnames rhs lhs
             pure (PatClause ploc newlhs newrhs)
    mkClauseWith drop wname wargnames lhs (WithClause ploc patlhs rig wval prf flags ws)
        = do log "declare.def.clause.with" 20 "WithClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             newwval <- withRHS ploc drop wname wargnames wval lhs
             ws' <- traverse (mkClauseWith (S drop) wname wargnames lhs) ws
             pure (WithClause ploc newlhs rig newwval prf flags ws')
    mkClauseWith drop wname wargnames lhs (ImpossibleClause ploc patlhs)
        = do log "declare.def.clause.with" 20 "ImpossibleClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             pure (ImpossibleClause ploc newlhs)

-- TODO: remove
nameListEq : (xs : SnocList Name) -> (ys : SnocList Name) -> Maybe (xs = ys)
nameListEq [<] [<] = Just Refl
nameListEq (xs :< x) (ys :< y) with (nameEq x y)
  nameListEq (xs :< x) (ys :< x) | (Just Refl) with (nameListEq xs ys)
    nameListEq (xs :< x) (xs :< x) | (Just Refl) | Just Refl= Just Refl
    nameListEq (xs :< x) (ys :< x) | (Just Refl) | Nothing = Nothing
  nameListEq (xs :< x) (ys :< y) | Nothing = Nothing
nameListEq _ _ = Nothing

-- Calculate references for the given name, and recursively if they haven't
-- been calculated already
calcRefs : {auto c : Ref Ctxt Defs} ->
           (runtime : Bool) -> (aTotal : Name) -> (fn : Name) -> Core ()
calcRefs rt at fn
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact fn (gamma defs)
              | _ => pure ()
         let PMDef r cargs tree_ct tree_rt pats = definition gdef
              | _ => pure () -- not a function definition
         let refs : Maybe (NameMap Bool)
                  = if rt then refersToRuntimeM gdef else refersToM gdef
         let Nothing = refs
              | Just _ => pure () -- already done
         let tree : CaseTree cargs = if rt then tree_rt else tree_ct
         let metas = CaseTree.getMetas tree
         traverse_ addToSave (keys metas)
         let refs_all = addRefs at metas tree
         refs <- ifThenElse rt
                    (dropErased (keys refs_all) refs_all)
                    (pure refs_all)
         ignore $ ifThenElse rt
            (addDef fn ({ refersToRuntimeM := Just refs } gdef))
            (addDef fn ({ refersToM := Just refs } gdef))
         traverse_ (calcRefs rt at) (keys refs)
  where
    dropErased : List Name -> NameMap Bool -> Core (NameMap Bool)
    dropErased [] refs = pure refs
    dropErased (n :: ns) refs
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => dropErased ns refs
             if multiplicity gdef /= erased
                then dropErased ns refs
                else dropErased ns (delete n refs)

-- Compile run time case trees for the given name
mkRunTime : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            FC -> Name -> Core ()
mkRunTime fc n
    = do logC "compile.casetree" 5 $ do pure $ "Making run time definition for " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | _ => pure ()
         let cov = gdef.totality.isCovering
         -- If it's erased at run time, don't build the tree
         when (not (isErased $ multiplicity gdef)) $ do
           let PMDef r cargs tree_ct _ pats = definition gdef
                | _ => pure () -- not a function definition
           let ty = type gdef
           -- Prepare RHS of definitions, by erasing 0-multiplicities, and
           -- finding any applications to specialise (partially evaluate)
           pats' <- traverse (toErased (location gdef) (getSpec (flags gdef)))
                             pats

           let clauses_init = map (toClause (location gdef)) pats'
           clauses <- case cov of
                           MissingCases _ => do log "compile.casetree.missing" 5 $ "Adding uncovered error to \{show clauses_init}"
                                                pure $ addErrorCase clauses_init
                           _ => pure clauses_init

           (rargs ** (tree_rt, _)) <- getPMDef (location gdef) RunTime n ty clauses
           logC "compile.casetree" 5 $ do
             tree_rt <- toFullNames tree_rt
             pure $ unlines
               [ show cov ++ ":"
               , "Runtime tree for " ++ show (fullname gdef) ++ ":"
               , show (indent 2 $ prettyTree tree_rt)
               ]
           log "compile.casetree" 10 $ show tree_rt
           log "compile.casetree.measure" 15 $ show (measure tree_rt)

           let Just Refl = nameListEq cargs rargs
                   | Nothing => throw (InternalError "WAT")
           ignore $ addDef n $
                       { definition := PMDef r rargs tree_ct tree_rt pats
                       } gdef
           -- If it's a case block, and not already set as inlinable or forced
           -- to not be inlinable, check if it's safe to inline
           when (caseName !(toFullNames n) && noInline (flags gdef)) $
             do inl <- canInlineCaseBlock n
                when inl $ do
                  logC "compiler.inline.eval" 5 $ do pure "Marking \{show !(toFullNames n)} for inlining in runtime case tree."
                  setFlag fc n Inline
  where
    -- check if the flags contain explicit inline or noinline directives:
    noInline : List DefFlag -> Bool
    noInline (Inline :: _)   = False
    noInline (NoInline :: _) = False
    noInline (x :: xs) = noInline xs
    noInline _ = True

    caseName : Name -> Bool
    caseName (CaseBlock _ _) = True
    caseName (NS _ n) = caseName n
    caseName _ = False

    mkCrash : {vars : _} -> String -> Term vars
    mkCrash msg
       = apply fc (Ref fc Func (UN $ Basic "prim__crash"))
               [Erased fc Placeholder, PrimVal fc (Str msg)]

    matchAny : Term vars -> Term vars
    matchAny (App fc f a) = App fc (matchAny f) (Erased fc Placeholder)
    matchAny tm = tm

    makeErrorClause : {vars : _} -> Env Term vars -> Term vars -> Clause
    makeErrorClause env lhs
        = MkClause env (matchAny lhs)
             (mkCrash ("Unhandled input for " ++ show n ++ " at " ++ show fc))

    addErrorCase : List Clause -> List Clause
    addErrorCase [] = []
    addErrorCase [MkClause env lhs rhs]
        = MkClause env lhs rhs :: makeErrorClause env lhs :: []
    addErrorCase (x :: xs) = x :: addErrorCase xs

    getSpec : List DefFlag -> Maybe (List (Name, Nat))
    getSpec [] = Nothing
    getSpec (PartialEval n :: _) = Just n
    getSpec (x :: xs) = getSpec xs

    toErased : FC -> Maybe (List (Name, Nat)) ->
               (vars ** (Env Term vars, Term vars, Term vars)) ->
               Core (vars ** (Env Term vars, Term vars, Term vars))
    toErased fc spec (_ ** (env, lhs, rhs))
        = do lhs_erased <- linearCheck fc linear True env lhs
             -- Partially evaluate RHS here, where appropriate
             rhs' <- applyTransforms env rhs
             rhs' <- applySpecialise env spec rhs'
             rhs_erased <- linearCheck fc linear True env rhs'
             pure (_ ** (env, lhs_erased, rhs_erased))

    toClause : FC -> (vars ** (Env Term vars, Term vars, Term vars)) -> Clause
    toClause fc (_ ** (env, lhs, rhs))
        = MkClause env lhs rhs

compileRunTime : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 FC -> Name -> Core ()
compileRunTime fc atotal
    = do defs <- get Ctxt
         traverse_ (mkRunTime fc) (toCompileCase defs)
         traverse_ (calcRefs True atotal) (toCompileCase defs)

         update Ctxt { toCompileCase := [] }

toPats : Clause -> (vs ** (Env Term vs, Term vs, Term vs))
toPats (MkClause {vars} env lhs rhs)
    = (_ ** (env, lhs, rhs))

warnUnreachable : {auto c : Ref Ctxt Defs} ->
                  Clause -> Core ()
warnUnreachable (MkClause env lhs rhs)
    = recordWarning (UnreachableClause (getLoc lhs) env lhs)

isAlias : RawImp -> Maybe ((FC, Name)                -- head symbol
                          , List (FC, (FC, String))) -- pattern variables
isAlias lhs
  = do let (hd, apps) = getFnArgs lhs []
       hd <- isIVar hd
       args <- traverse (isExplicit >=> bitraverse pure isIBindVar) apps
       pure (hd, args)

lookupOrAddAlias : {vars : _} ->
                   {auto m : Ref MD Metadata} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   {auto o : Ref ROpts REPLOpts} ->
                   List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
                   Name -> List ImpClause -> Core (Maybe GlobalDef)
lookupOrAddAlias eopts nest env fc n [cl@(PatClause _ lhs _)]
  = do defs <- get Ctxt
       log "declare.def.alias" 20 $ "Looking at \{show cl}"
       Nothing <- lookupCtxtExact n (gamma defs)
         | Just gdef => pure (Just gdef)
       -- No prior declaration:
       --   1) check whether it has the shape of an alias
       let Just (hd, args) = isAlias lhs
         | Nothing => pure Nothing
       --   2) check whether it could be a misspelling
       log "declare.def" 5 $
         "Missing type declaration for the alias "
         ++ show n
         ++ ". Checking first whether it is a misspelling."
       [] <- do -- get the candidates
                Just (str, kept) <- getSimilarNames n
                   | Nothing => pure []
                -- only keep the ones that haven't been defined yet
                decls <- for kept $ \ (cand, vis, weight) => do
                    Just gdef <- lookupCtxtExact cand (gamma defs)
                      | Nothing => pure Nothing -- should be impossible
                    let None = definition gdef
                      | _ => pure Nothing
                    pure (Just (cand, vis, weight))
                pure $ showSimilarNames (currentNS defs) n str $ catMaybes decls
          | (x :: xs) => throw (MaybeMisspelling (NoDeclaration fc n) (x ::: xs))
       --   3) declare an alias
       log "declare.def" 5 "Not a misspelling: go ahead and declare it!"
       processType eopts nest env fc top Public []
          -- See #3409
          $ MkImpTy fc (MkFCVal fc n) $ holeyType (map snd args)
       defs <- get Ctxt
       lookupCtxtExact n (gamma defs)

  where
    holeyType : List (FC, String) -> RawImp
    holeyType [] = Implicit fc False
    holeyType ((xfc, x) :: xs)
      = let xfc = virtualiseFC xfc in
        IPi xfc top Explicit (Just (UN $ Basic x)) (Implicit xfc False)
      $ holeyType xs

lookupOrAddAlias _ _ _ fc n _
  = do defs <- get Ctxt
       lookupCtxtExact n (gamma defs)

export
processDef : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
             Name -> List ImpClause -> Core ()
processDef opts nest env fc n_in cs_in
  = do n <- inCurrentNS n_in
       withDefStacked n $ do
         defs <- get Ctxt
         Just gdef <- lookupOrAddAlias opts nest env fc n cs_in
           | Nothing => noDeclaration fc n
         let None = definition gdef
              | _ => throw (AlreadyDefined fc n)
         let ty = type gdef
         -- a module's interface hash (what determines when the module has changed)
         -- should include the definition (RHS) of anything that is public (available
         -- at compile time for elaboration) _or_ inlined (dropped into destination definitions
         -- during compilation).
         let hashit = (collapseDefault $ visibility gdef) == Public || (Inline `elem` gdef.flags)
         let mult = if isErased (multiplicity gdef)
                       then erased
                       else linear
         nidx <- resolveName n

         -- Dynamically rebind default totality requirement to this function's totality requirement
         -- and use this requirement when processing `with` blocks
         log "declare.def" 5 $ "Traversing clauses of " ++ show n ++ " with mult " ++ show mult
         let treq = fromMaybe !getDefaultTotalityOption (findSetTotal (flags gdef))
         cs <- withTotality treq $
               traverse (checkClause mult (collapseDefault $ visibility gdef) treq
                                     hashit nidx opts nest env) cs_in

         let pats = map toPats (rights cs)

         (cargs ** (tree_ct, unreachable)) <-
             logTime 3 ("Building compile time case tree for " ++ show n) $
                getPMDef fc (CompileTime mult) n ty (rights cs)

         traverse_ warnUnreachable unreachable

         logC "declare.def" 2 $
                 do t <- toFullNames tree_ct
                    pure ("Case tree for " ++ show n ++ ": " ++ show t)

         -- check whether the name was declared in a different source file
         defs <- get Ctxt
         let pi = case lookup n (userHoles defs) of
                        Nothing => defaultPI
                        Just e => { externalDecl := e } defaultPI
         -- Add compile time tree as a placeholder for the runtime tree,
         -- but we'll rebuild that in a later pass once all the case
         -- blocks etc are resolved
         ignore $ addDef (Resolved nidx)
                  ({ definition := PMDef pi cargs tree_ct tree_ct pats
                   } gdef)

         when (collapseDefault (visibility gdef) == Public) $
             do let rmetas = getMetas tree_ct
                log "declare.def" 10 $ "Saving from " ++ show n ++ ": " ++ show (keys rmetas)
                traverse_ addToSave (keys rmetas)
         when (isUserName n && collapseDefault (visibility gdef) /= Private) $
             do let tymetas = getMetas (type gdef)
                traverse_ addToSave (keys tymetas)
         addToSave n

         -- Flag this name as one which needs compiling
         update Ctxt { toCompileCase $= (n ::) }

         atotal <- toResolvedNames (NS builtinNS (UN $ Basic "assert_total"))
         logTime 3 ("Building size change graphs " ++ show n) $
           when (not (InCase `elem` opts)) $
             do calcRefs False atotal (Resolved nidx)
                sc <- calculateSizeChange fc n
                setSizeChange fc n sc
                checkIfGuarded fc n

         md <- get MD -- don't need the metadata collected on the coverage check

         cov <- logTime 3 ("Checking Coverage " ++ show n) $ checkCoverage nidx ty mult cs
         setCovering fc n cov
         put MD md

         -- If we're not in a case tree, compile all the outstanding case
         -- trees.
         when (not (elem InCase opts)) $
              compileRunTime fc atotal
  where
    -- Move `withTotality` to Core.Context if we need it elsewhere
    ||| Temporarily rebind the default totality requirement (%default total/partial/covering).
    withTotality : TotalReq -> Lazy (Core a) -> Core a
    withTotality tot c = do
         defaultTotality <- getDefaultTotalityOption
         setDefaultTotalityOption tot
         x <- catch c (\error => do setDefaultTotalityOption defaultTotality
                                    throw error)
         setDefaultTotalityOption defaultTotality
         pure x


    simplePat : forall vars . Term vars -> Bool
    simplePat (Local _ _ _ _) = True
    simplePat (Erased _ _) = True
    simplePat (As _ _ _ p) = simplePat p
    simplePat _ = False

    -- Is the clause returned from 'checkClause' a catch all clause, i.e.
    -- one where all the arguments are variables? If so, no need to do the
    -- (potentially expensive) coverage check
    catchAll : Clause -> Bool
    catchAll (MkClause env lhs _)
       = all simplePat (getArgs lhs)

    -- Return 'Nothing' if the clause is impossible, otherwise return the
    -- checked clause (with implicits filled in, so that we can see if they
    -- match any of the given clauses)
    checkImpossible : Int -> RigCount -> ClosedTerm ->
                      Core (Maybe ClosedTerm)
    checkImpossible n mult tm
        = do itm <- unelabNoPatvars [] tm
             let itm = map rawName itm
             handleUnify
               (do ctxt <- get Ctxt
                   log "declare.def.impossible" 3 $ "Checking for impossibility: " ++ show itm
                   autoimp <- isUnboundImplicits
                   setUnboundImplicits True
                   (_, lhstm) <- bindNames False itm
                   setUnboundImplicits autoimp
                   (lhstm, _) <- elabTerm n (InLHS mult) [] (MkNested []) []
                                    (IBindHere fc COVERAGE lhstm) Nothing
                   defs <- get Ctxt
                   lhs <- normaliseHoles defs [] lhstm
                   if !(hasEmptyPat defs [] lhs)
                      then do log "declare.def.impossible" 5 "Some empty pat"
                              put Ctxt ctxt
                              pure Nothing
                      else do log "declare.def.impossible" 5 "No empty pat"
                              empty <- clearDefs ctxt
                              rtm <- closeEnv empty !(nf empty [] lhs)
                              put Ctxt ctxt
                              pure (Just rtm))
               (\err => do defs <- get Ctxt
                           if not !(recoverableErr defs err)
                              then do
                                log "declare.def.impossible" 5 "impossible because \{show err}"
                                pure Nothing
                              else pure (Just tm))
      where
        closeEnv : Defs -> NF [<] -> Core ClosedTerm
        closeEnv defs (NBind _ x (PVar _ _ _ _) sc)
            = closeEnv defs !(sc defs (toClosure defaultOpts [] (Ref fc Bound x)))
        closeEnv defs nf = quote defs [] nf

    getClause : Either RawImp Clause -> Core (Maybe Clause)
    getClause (Left rawlhs)
        = catch (do lhsp <- getImpossibleTerm env nest rawlhs
                    log "declare.def.impossible" 3 $ "Generated impossible LHS: " ++ show lhsp
                    pure $ Just $ MkClause [] lhsp (Erased (getFC rawlhs) Impossible))
                (\e => do log "declare.def" 5 $ "Error in getClause " ++ show e
                          pure Nothing)
    getClause (Right c) = pure (Just c)

    checkCoverage : Int -> ClosedTerm -> RigCount ->
                    List (Either RawImp Clause) ->
                    Core Covering
    checkCoverage n ty mult cs
        = do covcs' <- traverse getClause cs -- Make stand in LHS for impossible clauses
             log "declare.def" 5 $ unlines
               $ "Using clauses :"
               :: map (("  " ++) . show) !(traverse toFullNames covcs')
             let covcs = mapMaybe id covcs'
             (_ ** (ctree, _)) <-
                 getPMDef fc (CompileTime mult) (Resolved n) ty covcs
             logC "declare.def" 3 $ do pure $ "Working from " ++ show !(toFullNames ctree)
             missCase <- if any catchAll covcs
                            then do logC "declare.def" 3 $ do pure "Catch all case in \{show !(getFullName (Resolved n))}"
                                    pure []
                            else getMissing fc (Resolved n) ctree
             logC "declare.def" 3 $
                     do mc <- traverse toFullNames missCase
                        pure ("Initially missing in " ++
                                 show !(getFullName (Resolved n)) ++ ":\n" ++
                                showSep "\n" (map show mc))
             -- Filter out the ones which are impossible
             missImp <- traverse (checkImpossible n mult) missCase
             -- Filter out the ones which are actually matched (perhaps having
             -- come up due to some overlapping patterns)
             missMatch <- traverse (checkMatched covcs) (mapMaybe id missImp)
             let miss = catMaybes missMatch
             if isNil miss
                then do [] <- getNonCoveringRefs fc (Resolved n)
                           | ns => toFullNames (NonCoveringCall ns)
                        pure IsCovering
                else pure (MissingCases miss)
