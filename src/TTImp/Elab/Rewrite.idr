module TTImp.Elab.Rewrite

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.GetType
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

%default covering

-- TODO: Later, we'll get the name of the lemma from the type, if it's one
-- that's generated for a dependent type. For now, always return the default
findRewriteLemma : {auto c : Ref Ctxt Defs} ->
                   FC -> (rulety : Term vars) ->
                   Core Name
findRewriteLemma loc rulety
   = case !getRewrite of
          Nothing => throw (GenericMsg loc "No rewrite lemma defined")
          Just n => pure n

getRewriteTerms : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  FC -> Defs -> NF vars -> Error ->
                  Core (NF vars, NF vars, NF vars)
getRewriteTerms loc defs (NTCon nfc eq t a args) err
    = if !(isEqualTy eq)
         then case reverse $ map snd args of
                   (rhs :: lhs :: rhsty :: lhsty :: _) =>
                        pure (!(evalClosure defs lhs),
                              !(evalClosure defs rhs),
                              !(evalClosure defs lhsty))
                   _ => throw err
         else throw err
getRewriteTerms loc defs ty err
    = throw err

rewriteErr : Error -> Bool
rewriteErr (NotRewriteRule _ _ _) = True
rewriteErr (RewriteNoChange _ _ _ _) = True
rewriteErr (InType _ _ err) = rewriteErr err
rewriteErr (InCon _ _ err) = rewriteErr err
rewriteErr (InLHS _ _ err) = rewriteErr err
rewriteErr (InRHS _ _ err) = rewriteErr err
rewriteErr (WhenUnifying _ _ _ _ _ err) = rewriteErr err
rewriteErr _ = False

record Lemma (vars : _) where
  constructor MkLemma
  ||| The name of the rewriting lemma
  name : Name
  ||| The predicate (\ v => lhs === rhs) to pass to it
  pred : Term vars
  ||| The type ((v : ?) -> Type) of the predicate
  predTy : Term vars

elabRewrite : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> Env Term vars ->
              (expected : Term vars) ->
              (rulety : Term vars) ->
              Core (Lemma vars)
elabRewrite loc env expected rulety
    = do defs <- get Ctxt
         parg <- genVarName "rwarg"
         tynf <- nf defs env rulety
         (lt, rt, lty) <- getRewriteTerms loc defs tynf (NotRewriteRule loc env rulety)
         lemn <- findRewriteLemma loc rulety

         -- Need to normalise again, since we might have been delayed and
         -- the metavariables might have been updated
         expnf <- nf defs env expected

         logNF "elab.rewrite" 5 "Rewriting" env lt
         logNF "elab.rewrite" 5 "Rewriting in" env expnf
         rwexp_sc <- replace defs env lt (Ref loc Bound parg) expnf
         logTerm "elab.rewrite" 5 "Rewritten to" rwexp_sc

         empty <- clearDefs defs
         let pred = Bind loc parg (Lam loc top Explicit
                          !(quote empty env lty))
                          (refsToLocals (Add parg parg None) rwexp_sc)
         gpredty <- getType env pred
         predty <- getTerm gpredty
         exptm <- quote defs env expected

         -- if the rewritten expected type converts with the original,
         -- then the rewrite did nothing, which is an error
         when !(convert defs env rwexp_sc exptm) $
             throw (RewriteNoChange loc env rulety exptm)
         pure (MkLemma lemn pred predty)

export
checkRewrite : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> RawImp -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRewrite rigc elabinfo nest env fc rule tm Nothing
    = throw (GenericMsg fc "Can't infer a type for rewrite")
checkRewrite {vars} rigc elabinfo nest env ifc rule tm (Just expected)
    = delayOnFailure ifc rigc env (Just expected) rewriteErr Rewrite $ \delayed =>
        do let vfc = virtualiseFC ifc

           constart <- getNextEntry
           (rulev, grulet) <- check erased elabinfo nest env rule Nothing
           solveConstraintsAfter constart inTerm Normal

           rulet <- getTerm grulet
           expTy <- getTerm expected
           when delayed $ log "elab.rewrite" 5 "Retrying rewrite"
           lemma <- elabRewrite vfc env expTy rulet

           rname <- genVarName "_"
           pname <- genVarName "_"

           let pbind = Let vfc erased lemma.pred lemma.predTy
           let rbind = Let vfc erased (weaken rulev) (weaken rulet)

           let env' = rbind :: pbind :: env

           -- Nothing we do in this last part will affect the EState,
           -- we're only doing the application this way to make sure the
           -- implicits for the rewriting lemma are in the right place. But,
           -- we still need the right type for the EState, so weaken it once
           -- for each of the let bindings above.
           (rwtm, grwty) <-
              inScope vfc (pbind :: env) $ \e' =>
                inScope {e=e'} vfc env' $ \e'' =>
                  let offset = mkSizeOf [rname, pname] in
                  check {e = e''} rigc elabinfo (weakenNs offset nest) env'
                    (apply (IVar vfc lemma.name)
                      [ IVar vfc pname
                      , IVar vfc rname
                      , tm ])
                    (Just (gnf env' (weakenNs offset expTy)))
           rwty <- getTerm grwty
           let binding = Bind vfc pname pbind . Bind vfc rname rbind
           pure (binding rwtm, gnf env (binding rwty))
