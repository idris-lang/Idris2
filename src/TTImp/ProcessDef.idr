module TTImp.ProcessDef

import Core.Context.Pretty
import Core.Case.CaseBuilder
import Core.Case.CaseTree
import Core.Coverage
import Core.Env
import Core.Erase
import Core.Hash
import Core.LinearCheck
import Core.Metadata
import Core.Termination
import Core.Termination.CallGraph
import Core.Transform
import Core.Evaluate.Value
import Core.Evaluate.Normalise
import Core.Evaluate.Quote
import Core.Evaluate.Expand
import Core.Evaluate
import Core.UnifyState

import Idris.REPL.Opts
import Idris.Syntax
import Idris.Pretty.Annotations

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Binders
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Impossible
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
import Libraries.Data.SnocList.SizeOf

%default covering

mutual
  mismatchNF : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               NF vars -> NF vars -> Core Bool
  mismatchNF (VTCon _ xn _ xargs) (VTCon _ yn _ yargs)
      = if xn /= yn
          then pure True
          else do xargsNF <- traverseSnocList value xargs
                  yargsNF <- traverseSnocList value yargs
                  anyM mismatch (zip xargsNF yargsNF)
  mismatchNF (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
      = if xt /= yt
          then pure True
          else do xargsNF <- traverseSnocList value xargs
                  yargsNF <- traverseSnocList value yargs
                  anyM mismatch (zip xargsNF yargsNF)
  mismatchNF (VPrimVal _ xc) (VPrimVal _ yc) = pure (xc /= yc)
  mismatchNF (VDelayed _ _ x) (VDelayed _ _ y)
      = mismatchNF !(expand x) !(expand y)
  mismatchNF (VDelay _ _ _ x) (VDelay _ _ _ y)
      = mismatchNF !(expand x) !(expand y)

  -- NPrimVal is apart from NDCon, NTCon, NBind, and NType
  mismatchNF (VPrimVal {}) (VDCon {}) = pure True
  mismatchNF (VDCon {}) (VPrimVal {}) = pure True
  mismatchNF (VPrimVal {}) (VBind {}) = pure True
  mismatchNF (VBind {}) (VPrimVal {}) = pure True
  mismatchNF (VPrimVal {}) (VTCon {}) = pure True
  mismatchNF (VTCon {}) (VPrimVal {}) = pure True
  mismatchNF (VPrimVal {}) (VType {}) = pure True
  mismatchNF (VType {}) (VPrimVal {}) = pure True

  -- NTCon is apart from NBind, and NType
  mismatchNF (VTCon {}) (VBind {}) = pure True
  mismatchNF (VBind {}) (VTCon {}) = pure True
  mismatchNF (VTCon {}) (VType {}) = pure True
  mismatchNF (VType {}) (VTCon {}) = pure True

  -- NBind is apart from NType
  mismatchNF (VBind {}) (VType {}) = pure True
  mismatchNF (VType {}) (VBind {}) = pure True

  mismatchNF _ _ = pure False

  mismatch : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             (Glued vars, Glued vars) -> Core Bool
  mismatch (x, y)
      = mismatchNF !(expand x) !(expand y)

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
export
impossibleOK : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               NF vars -> NF vars -> Core Bool
impossibleOK (VTCon _ xn xa xargs) (VTCon _ yn ya yargs)
    = if xn /= yn
         then pure True
         else do xargsNF <- traverseSnocList value xargs
                 yargsNF <- traverseSnocList value yargs
                 anyM mismatch (zip xargsNF yargsNF)
-- If it's a data constructor, any mismatch will do
impossibleOK (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else do xargsNF <- traverseSnocList value xargs
                 yargsNF <- traverseSnocList value yargs
                 anyM mismatch (zip xargsNF yargsNF)
impossibleOK (VPrimVal _ x) (VPrimVal _ y) = pure (x /= y)

-- VPrimVal is apart from VDCon, VTCon, VBind, and VType
impossibleOK (VPrimVal {}) (VDCon {}) = pure True
impossibleOK (VDCon {}) (VPrimVal {}) = pure True
impossibleOK (VPrimVal {}) (VBind {}) = pure True
impossibleOK (VBind {}) (VPrimVal {}) = pure True
impossibleOK (VPrimVal {}) (VTCon {}) = pure True
impossibleOK (VTCon {}) (VPrimVal {}) = pure True
impossibleOK (VPrimVal {}) (VType {}) = pure True
impossibleOK (VType {}) (VPrimVal {}) = pure True

-- VTCon is apart from VBind, and VType
impossibleOK (VTCon {}) (VBind {}) = pure True
impossibleOK (VBind {}) (VTCon {}) = pure True
impossibleOK (VTCon {}) (VType {}) = pure True
impossibleOK (VType {}) (VTCon {}) = pure True

-- VBind is apart from VType
impossibleOK (VBind {}) (VType {}) = pure True
impossibleOK (VType {}) (VBind {}) = pure True

impossibleOK x y = pure False

export
impossibleErrOK : {auto c : Ref Ctxt Defs} ->
                  Error -> Core Bool
impossibleErrOK (CantConvert fc gam env l r)
    = do defs' <- get Ctxt
         put Ctxt ({ gamma := gam } defs')
         res <- impossibleOK !(expand !(nf env l))
                             !(expand !(nf env r))
         put Ctxt defs'
         pure res
impossibleErrOK (CantSolveEq fc gam env l r)
    = do defs' <- get Ctxt
         put Ctxt ({ gamma := gam } defs')
         res <- impossibleOK !(expand !(nf env l))
                             !(expand !(nf env r))
         put Ctxt defs'
         pure res
impossibleErrOK (BadDotPattern _ _ ErasedArg _ _) = pure True
impossibleErrOK (CyclicMeta _ _ _ _) = pure True
impossibleErrOK (AllFailed errs)
    = anyM impossibleErrOK (map snd errs)
impossibleErrOK (WhenUnifying _ _ _ _ _ err)
    = impossibleErrOK err
impossibleErrOK ImpossibleCase = pure True
impossibleErrOK _ = pure False

-- If it's a clause we've generated, see if the error is recoverable. That
-- is, if we have a concrete thing, and we're expecting the same concrete
-- thing, or a function of something, then we might have a match.
export
recoverable : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              NF vars -> NF vars -> Core Bool
-- Unlike the above, any mismatch will do

-- TYPE CONSTRUCTORS
recoverable (VTCon _ xn xa xargs) (VTCon _ yn ya yargs)
    = if xn /= yn
         then pure False
         else do xargsNF <- traverseSnocList value xargs
                 yargsNF <- traverseSnocList value yargs
                 pure $ not !(anyM mismatch (zip xargsNF yargsNF))
-- Type constructor vs. primitive type
recoverable (VTCon _ _ _ _) (VPrimVal _ _) = pure False
recoverable (VPrimVal _ _) (VTCon _ _ _ _) = pure False
-- Type constructor vs. type
recoverable (VTCon _ _ _ _) (VType _ _) = pure False
recoverable (VType _ _) (VTCon _ _ _ _) = pure False
-- Type constructor vs. binder
recoverable (VTCon _ _ _ _) (VBind _ _ _ _) = pure False
recoverable (VBind _ _ _ _) (VTCon _ _ _ _) = pure False

recoverable (VTCon _ _ _ _) _ = pure True
recoverable _ (VTCon _ _ _ _) = pure True

-- DATA CONSTRUCTORS
recoverable (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure False
         else do xargsNF <- traverseSnocList value xargs
                 yargsNF <- traverseSnocList value yargs
                 pure $ not !(anyM mismatch (zip xargsNF yargsNF))
-- Data constructor vs. primitive constant
recoverable (VDCon _ _ _ _ _) (VPrimVal _ _) = pure False
recoverable (VPrimVal _ _) (VDCon _ _ _ _ _) = pure False

recoverable (VDCon _ _ _ _ _) _ = pure True
recoverable _ (VDCon _ _ _ _ _) = pure True

-- FUNCTION CALLS
recoverable (VApp _ _ _ _ _) (VApp _ _ _ _ _)
    = pure True -- both functions; recoverable

-- PRIMITIVES
recoverable (VPrimVal _ x) (VPrimVal _ y) = pure (x == y)
-- primitive vs. binder
recoverable (VPrimVal _ _) (VBind _ _ _ _) = pure False
recoverable (VBind _ _ _ _) (VPrimVal _ _) = pure False

-- OTHERWISE: no
recoverable x y = pure False

export
recoverableErr : {auto c : Ref Ctxt Defs} ->
                 Error -> Core Bool
recoverableErr (CantConvert fc gam env l r)
  = do defs' <- get Ctxt
       put Ctxt ({ gamma := gam } defs')
       ok <- recoverable !(expand !(nf env l))
                         !(expand !(nf env r))
       put Ctxt defs'
       pure ok

recoverableErr (CantSolveEq fc gam env l r)
  = do defs' <- get Ctxt
       put Ctxt ({ gamma := gam } defs')
       ok <- recoverable !(expand !(nf env l))
                         !(expand !(nf env r))
       put Ctxt defs'
       pure ok
recoverableErr (BadDotPattern _ _ ErasedArg _ _) = pure True
recoverableErr (AllFailed errs)
    = anyM recoverableErr (map snd errs)
recoverableErr (WhenUnifying _ _ _ _ _ err)
    = recoverableErr err
recoverableErr _ = pure False

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
extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy {}) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy {}) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n (PVTy {}) tysc) | (Just Refl)
      = extendEnv (Env.bind env $ PVar fc c pi tmty) (Drop p) (weaken (dropName n nest)) sc tysc
extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet {}) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet {}) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  -- PLet on the left becomes Let on the right, to give it computational force
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n (PLet {}) tysc) | (Just Refl)
      = extendEnv (Env.bind env $ Let fc c tmval tmty) (Drop p) (weaken (dropName n nest)) sc tysc
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
                    logTerm "declare.def.lhs" 5 ("Type of " ++ show !(toFullNames n)) nty
                    logTermNF "declare.def.lhs" 5 ("Type NF of " ++ show !(toFullNames n)) Env.empty nty
                    log "declare.def.lhs" 5 ("Args: " ++ show !(traverse toFullNames args))
                    findLinArg (accessible nt rig) !(expand !(nf Env.empty nty)) args
           _ => pure []
    where
      accessible : NameType -> RigCount -> RigCount
      accessible Func r = if top then r else erased
      accessible _ r = r

      findLinArg : {vars : _} ->
                   RigCount -> ClosedNF -> List (Term vars) ->
                   Core (List (Name, RigCount))
      findLinArg rig ty@(VBind _ _ (Pi _ c _ _) _) (As fc u a p :: as)
          = if isLinear c
               then case u of
                         UseLeft => findLinArg rig ty (p :: as)
                         UseRight => findLinArg rig ty (a :: as)
               -- Yaffle: else findLinArg rig ty (as :< p :< a)
               else pure $ !(findLinArg rig ty [a]) ++ !(findLinArg rig ty (p :: as))
      findLinArg rig (VBind _ x (Pi _ c _ _) sc) (Local {name=a} fc _ idx prf :: as)
          = do defs <- get Ctxt
               let a = nameAt prf
               if idx < bound
                 then do sc' <- expand !(sc (pure (vRef fc Bound x)))
                         pure $ (a, rigMult c rig) ::
                                    !(findLinArg rig sc' as)
                 else do sc' <- expand !(sc (pure (vRef fc Bound x)))
                         findLinArg rig sc' as
      findLinArg rig (VBind fc x (Pi _ c _ _) sc) (a :: as)
          = do defs <- get Ctxt
               pure $ !(findLinear False bound (c |*| rig) a) ++
                      !(findLinArg rig !(expand !(sc (pure (vRef fc Bound x)))) as)
      findLinArg rig ty (a :: as)
          = pure $ !(findLinear False bound rig a) ++ !(findLinArg rig ty as)
      findLinArg _ _ [] = pure []

setLinear : List (Name, RigCount) -> Term vars -> Term vars
setLinear vs tm@(Bind fc x b sc)
    = if isPatternBinder b
         then let b' = maybe b (setMultiplicity b) (lookup x vs)
               in Bind fc x b' (setLinear vs sc)
         else tm
  where
    isPatternBinder : Binder a -> Bool
    isPatternBinder (PVar {}) = True
    isPatternBinder (PVTy {}) = True
    isPatternBinder (PLet {}) = True
    isPatternBinder _ = False
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
                   else implicitsAs n defs (asList vars) lhs_bound

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
         lhsty <- quote env lhstyg

         defs <- get Ctxt
         let lhsenv = letToLam env
         -- we used to fully normalise the LHS, to make sure fromInteger
         -- patterns were allowed, but now they're fully normalised anyway
         -- so we only need to do the holes. If there's a lot of type level
         -- computation, this is a huge saving!
         lhstm <- normaliseHoles lhsenv lhstm
         lhsty <- normaliseHoles env lhsty
         linvars_in <- findLinear True 0 linear lhstm
         logTerm "declare.def.lhs" 10 "Checked LHS term after normalise" lhstm
         log "declare.def.lhs" 5 $ "Linearity of names in " ++ show n ++ ": " ++
                 show linvars_in

         logTerm "declare.def.lhs" 10 "lhsty" lhsty
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
   = pure $ !(isEmpty defs env !(expand !(nf env (binderType b))))
            || !(hasEmptyPat defs (Env.bind env b) sc)
hasEmptyPat defs env _ = pure False

-- For checking with blocks as nested names
applyEnv : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Env Term vars -> Name ->
           Core (Name, (Maybe Name, List (Var vars), FC -> NameType -> Term vars))
applyEnv env withname
    = do n' <- resolveName withname
         pure (withname, (Just withname, VarSet.asList $ allVarsNoLet env,
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
                                      (IBindHere fc COVERAGE lhs) Nothing
               defs <- get Ctxt
               lhs <- normaliseHoles env lhstm
               if !(hasEmptyPat defs env lhs)
                  then pure (Left lhs_raw)
                  else throw (ValidCase fc env (Left lhs)))
           (\err =>
              case err of
                   ValidCase {} => throw err
                   _ => do if !(impossibleErrOK err)
                              then pure (Left lhs_raw)
                              else throw (ValidCase fc env (Right err)))
checkClause {vars} mult vis totreq hashit n opts nest env (PatClause fc lhs_in rhs)
    = do (_, (vars'  ** (sub', env', nest', lhstm', lhsty'))) <-
             checkLHS False mult n opts nest env fc lhs_in
         let rhsMode = if isErased mult then InType else InExpr
         log "declare.def.clause" 5 $ "Checking RHS " ++ show rhs
         logEnv "declare.def.clause" 5 "In env" env'
         logTerm "declare.def.clause" 5 "lhsty_backtick" lhsty'

         lhsty' <- nf env' lhsty'
         logNF "declare.def.clause" 5 "lhsty_backtick NF" env' lhsty'

         rhstm <- logTime 3 ("Check RHS " ++ show fc) $
                    wrapErrorC opts (InRHS fc !(getFullName (Resolved n))) $
                       checkTermSub n rhsMode opts nest' env' env sub' rhs lhsty'
         clearHoleLHS

         logTerm "declare.def.clause" 3 "RHS term" rhstm
         when hashit $
           do addHashWithNames lhstm'
              addHashWithNames rhstm
              log "module.hash" 15 "Adding hash for def."

         -- If the rhs is a hole, record the lhs in the metadata because we
         -- might want to split it interactively
         case rhstm of
              Meta {} =>
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
         wvalTy <- quote env' gwvalTy
         wval <- normaliseHoles env' wval
         wvalTy <- normaliseHoles env' wvalTy

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
         logTerm "declare.def.clause.with" 5 "notreqty" notreqty

         let repFn = if Syntactic `elem` flags
                       then replaceSyn
                       else replace
         wtyScope <- repFn scenv !(nf scenv (weakenNs (mkSizeOf wargs) wval))
                            var
                            !(nf scenv
                                 (weakenNs (mkSizeOf wargs) notreqty))
         logTerm "declare.def.clause.with" 3 "wtyScope" wtyScope

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
                          !(nf env' reqty)

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

    bindWithArgs :
       (rig : RigCount) -> (wvalTy : Term xs) -> Maybe ((RigCount, Name), Term xs) ->
       (wvalEnv : Env Term xs) ->
       Core (ext : Scope
         ** ( Env Term (Scope.addInner xs ext)
            , Term (Scope.addInner xs ext)
            , (Term (Scope.addInner xs ext) -> Term xs)
            ))
    bindWithArgs {xs} rig wvalTy Nothing wvalEnv =
      let wargn : Name
          wargn = MN "warg" 0
          wargs : Scope
          wargs = [<wargn]

          scenv : Env Term (Scope.addInner xs wargs)
                := wvalEnv :< Pi vfc top Explicit wvalTy

          var : Term (Scope.addInner xs wargs)
              := Local vfc (Just False) Z First

          binder : Term (Scope.addInner xs wargs) -> Term xs
                 := Bind vfc wargn (Pi vfc rig Explicit wvalTy)

      in pure (wargs ** (scenv, var, binder))

    bindWithArgs {xs} rig wvalTy (Just ((rigPrf, name), wval)) wvalEnv = do
      defs <- get Ctxt

      let eqName = NS builtinNS (UN $ Basic "Equal")
      Just (TCon ar _ _ _ _ _ _) <- lookupDefExact eqName (gamma defs)
        | _ => throw (InternalError "Cannot find builtin Equal")
      let eqTyCon = Ref vfc (TyCon ar) !(toResolvedNames eqName)

      let wargn : Name
          wargn = MN "warg" 0
          wargs : Scope
          wargs = [<wargn, name]

          wvalTy' := weaken wvalTy
          eqTy : Term (xs :< MN "warg" 0)
               := apply vfc eqTyCon
                           [ (erased, wvalTy')
                           , (erased, wvalTy')
                           , (top, weaken wval)
                           , (top, Local vfc (Just False) Z First)
                           ]

          scenv : Env Term (Scope.addInner xs wargs)
                := wvalEnv
                :< Pi vfc top Explicit wvalTy
                :< Pi vfc top Implicit eqTy

          var : Term (Scope.addInner xs wargs)
              := Local vfc (Just False) (S Z) (Later First)

          binder : Term (Scope.addInner xs wargs) -> Term xs
                 := \ t => Bind vfc wargn (Pi vfc rig Explicit wvalTy)
                         $ Bind vfc name  (Pi vfc rigPrf Implicit eqTy) t

      pure (wargs ** (scenv, var, binder))

    -- If it's 'Keep/Refl' in 'outprf', that means it was in the outer
    -- environment so we need to keep it in the same place in the 'with'
    -- function. Hence, turn it to Keep whatever
    keepOldEnv : {0 outer : _} -> {vs : _} ->
                 (outprf : Thin outer vs) -> Thin vs' vs ->
                 (vs'' : Scope ** Thin vs'' vs)
    keepOldEnv {vs} Refl p = (vs ** Refl)
    keepOldEnv {vs} p Refl = (vs ** Refl)
    keepOldEnv {vs = _ :< _} (Drop p) (Drop p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** Drop rest)
    keepOldEnv {vs = _ :< _} (Drop p) (Keep p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** Keep rest)
    keepOldEnv {vs = _ :< _} (Keep p) (Drop p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** Keep rest)
    keepOldEnv {vs = _ :< _} (Keep p) (Keep p')
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

-- Calculate references for the given name, and recursively if they haven't
-- been calculated already
calcRefs : {auto c : Ref Ctxt Defs} ->
           (runtime : Bool) -> (aTotal : Name) -> (fn : Name) -> Core ()
calcRefs rt at fn
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact fn (gamma defs)
              | _ => pure ()
         let Function r tree_ct tree_rt pats = definition gdef
              | _ => pure () -- not a function definition
         let refs : Maybe (NameMap Bool)
                  = if rt then refersToRuntimeM gdef else refersToM gdef
         let Nothing = refs
              | Just _ => pure () -- already done
         let tree : Term [<] = if rt then tree_rt else tree_ct
         let metas = TT.getMetas tree
         traverse_ addToSave (keys metas)
         let refs_all = TT.addRefs False at metas tree
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
            FC -> (CaseType, Name) -> Core ()
mkRunTime fc (ct, n)
    = do logC "compile.casetree" 5 $ do pure $ "Making run time definition for " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | _ => pure ()
         let cov = gdef.totality.isCovering
         -- If it's erased at run time, don't build the tree
         when (not (isErased $ multiplicity gdef)) $ do
           let Function r tree_ct _ (Just pats) = definition gdef
                | _ => pure () -- not a function definition
           let ty = type gdef
           -- Prepare RHS of definitions, by erasing 0-multiplicities, and
           -- finding any applications to specialise (partially evaluate)
           pats' <- traverse (toErased (location gdef) (getSpec (flags gdef))) pats

           clauses <- case cov of
                           MissingCases _ => do log "compile.casetree.missing" 5 $ "Adding uncovered error to \{show pats'}"
                                                pure $ addErrorCase pats'
                           _ => pure pats'

           (tree_rt, _) <- getPMDef (location gdef) ct RunTime n ty clauses
           logC "compile.casetree" 5 $ do
             tree_rt <- toFullNames tree_rt
             pure $ unlines
               [ show cov ++ ":"
               , "Runtime tree for " ++ show (fullname gdef) ++ ":"
               , show (indent 2 $ prettyTree tree_rt)
               ]
           ignore $ addDef n $
                       { definition := Function r tree_ct tree_rt (Just pats)
                       } gdef
  where
    mkCrash : {vars : _} -> String -> Term vars
    mkCrash msg
       = apply fc (Ref fc Func (UN $ Basic "prim__crash"))
               [(erased, Erased fc Placeholder),
                (top, PrimVal fc (Str msg))]

    matchAny : Term vars -> Term vars
    matchAny (App fc f c a) = App fc (matchAny f) c (Erased fc Placeholder)
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
               Clause ->
               Core Clause
    toErased fc spec (MkClause env lhs rhs)
        = do lhs_erased <- erase linear env lhs
             -- Partially evaluate RHS here, where appropriate
             rhs' <- applyTransforms env rhs
             -- Yaffle has no it
             -- rhs' <- applySpecialise env spec rhs'
             rhs_erased <- erase linear env rhs'
             pure (MkClause env lhs_erased rhs_erased)

compileRunTime : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 FC -> Name -> Core ()
compileRunTime fc atotal
    = do defs <- get Ctxt
         traverse_ (mkRunTime fc) (toCompileCase defs)
         traverse_ (calcRefs True atotal) (map snd $ toCompileCase defs)

         update Ctxt { toCompileCase := [] }

warnUnreachable : {auto c : Ref Ctxt Defs} ->
                  Clause -> Core ()
warnUnreachable (MkClause env lhs rhs)
    = recordWarning (UnreachableClause (getLoc lhs) env lhs)

isAlias : RawImp -> Maybe ((FC, Name)              -- head symbol
                          , List (FC, (FC, Name))) -- pattern variables
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
          $ Mk [fc, MkFCVal fc n] $ holeyType (map snd args)
       defs <- get Ctxt
       lookupCtxtExact n (gamma defs)

  where
    holeyType : List (FC, Name) -> RawImp
    holeyType [] = Implicit fc False
    holeyType ((xfc, x) :: xs)
      = let xfc = virtualiseFC xfc in
        IPi xfc top Explicit (Just x) (Implicit xfc False)
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
         logC "declare.def" 50 $ do pure "For \{show n} NS: \{show $ (!getNS :: !getNestedNS)}"

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
         log "declare.def" 5 $ "Traversing clauses of " ++ show n ++ " with mult " ++ show mult ++ " in " ++ show cs_in
         let treq = fromMaybe !getDefaultTotalityOption (findSetTotal (flags gdef))
         cs <- withTotality treq $
               traverse (checkClause mult (collapseDefault $ visibility gdef) treq
                                     hashit nidx opts nest env) cs_in

         let pats = rights cs

         let ct = if elem InCase opts then CaseBlock n else PatMatch
         (tree_ct, unreachable) <-
             logTime 3 ("Building compile time case tree for " ++ show n) $
                getPMDef fc ct (CompileTime mult) n ty pats

         traverse_ warnUnreachable unreachable

         logC "declare.def" 2 $
                 do t <- toFullNames tree_ct
                    pure $ unlines
                      [ "Compile time tree for " ++ show (fullname gdef) ++ ":"
                      , show (indent 2 $ prettyTree t)
                      ]
         -- check whether the name was declared in a different source file
         defs <- get Ctxt
         let pi = case lookup n (userHoles defs) of
                        Nothing => defaultPI
                        Just e => { externalDecl := e } defaultPI
         -- Add compile time tree as a placeholder for the runtime tree,
         -- but we'll rebuild that in a later pass once all the case
         -- blocks etc are resolved
         ignore $ addDef (Resolved nidx)
                  ({ definition := Function pi tree_ct tree_ct (Just pats)
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
         update Ctxt { toCompileCase $= ((ct, n) ::) }

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
    simplePat (Local {}) = True
    simplePat (Erased {}) = True
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
        = do itm <- unelabNoPatvars Env.empty tm
             let itm = map rawName itm
             handleUnify
               (do ctxt <- get Ctxt
                   log "declare.def.impossible" 3 $ "Checking for impossibility: " ++ show itm
                   autoimp <- isUnboundImplicits
                   setUnboundImplicits True
                   (_, lhstm) <- bindNames False itm
                   setUnboundImplicits autoimp
                   (lhstm, _) <- elabTerm n (InLHS mult) [] (NestedNames.empty) Env.empty
                                    (IBindHere fc COVERAGE lhstm) Nothing
                   defs <- get Ctxt
                   lhs <- normaliseHoles Env.empty lhstm
                   if !(hasEmptyPat defs Env.empty lhs)
                      then do log "declare.def.impossible" 5 "Some empty pat"
                              put Ctxt ctxt
                              pure Nothing
                      else do log "declare.def.impossible" 5 "No empty pat"
                              empty <- clearDefs ctxt
                              rtm <- closeEnv !(nf Env.empty lhs)
                              put Ctxt ctxt
                              pure (Just rtm))
               (\err => do defs <- get Ctxt
                           if !(impossibleErrOK err)
                              then do
                                log "declare.def.impossible" 5 "impossible because \{show err}"
                                pure Nothing
                              else pure (Just tm))
      where
        -- They'll be 'Bind' at the top level already, and we really don't
        -- want to expand when we get to the clause, so 'Glued' is what we
        -- want here.
        closeEnv : Glued Scope.empty -> Core ClosedTerm
        closeEnv (VBind _ x (PVar {}) sc)
            = closeEnv !(sc (pure (vRef fc Bound x)))
        closeEnv nf = quote Env.empty nf

    getClause : Either RawImp Clause -> Core (Maybe Clause)
    getClause (Left rawlhs)
        = catch (do lhsp <- getImpossibleTerm env nest rawlhs
                    log "declare.def.impossible" 3 $ "Generated impossible LHS: " ++ show lhsp
                    pure $ Just $ MkClause Env.empty lhsp (Erased (getFC rawlhs) Impossible))
                (\e => do log "declare.def" 5 $ "Error in getClause " ++ show e
                          recordWarning $ GenericWarn (fromMaybe (getFC rawlhs) $ getErrorLoc e) (show e)
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
             (ctree, _) <-
                 getPMDef fc PatMatch (CompileTime mult) (Resolved n) ty covcs
             logC "declare.def" 3 $ do pure $ "Working from " ++ show !(toFullNames ctree)
             missCase <- if any catchAll covcs
                            then do logC "declare.def" 3 $ do pure "Catch all case in \{show !(getFullName (Resolved n))}"
                                    pure []
                            else getMissing fc (Resolved n) ty ctree
             logC "declare.def" 3 $
                     do mc <- traverse toFullNames missCase
                        pure ("Initially missing in " ++
                                 show !(getFullName (Resolved n)) ++ ":\n" ++
                                joinBy "\n" (map show mc))
             -- Filter out the ones which are impossible
             missImp <- traverse (checkImpossible n mult) missCase
             -- Filter out the ones which are actually matched (perhaps having
             -- come up due to some overlapping patterns)
             missMatch <- traverse (checkMatched (not $ isErased mult) covcs) (mapMaybe id missImp)
                                              -- ^ Do not check coverage for erased arguments
                                              -- only in non-erased functions (Issues #1998, #3357)
             let miss = catMaybes missMatch
             if isNil miss
                then do [] <- getNonCoveringRefs fc (Resolved n)
                           | ns => toFullNames (NonCoveringCall ns)
                        pure IsCovering
                else pure (MissingCases miss)
