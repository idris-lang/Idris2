module TTImp.Elab.Lazy

import Core.Env
import Core.Metadata
import Core.Unify
import Core.Evaluate.Value
import Core.Evaluate.Expand
import Core.Evaluate

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

%default covering

export
checkDelayed : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> LazyReason -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkDelayed rig elabinfo nest env fc r tm exp
    = do u <- uniVar fc
         (tm', gty) <- check rig elabinfo nest env tm (Just (gType fc u))
         pure (TDelayed fc r tm', gty)

export
checkDelay : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             RigCount -> ElabInfo ->
             NestedNames vars -> Env Term vars ->
             FC -> RawImp -> Maybe (Glued vars) ->
             Core (Term vars, Glued vars)
checkDelay rig elabinfo nest env fc tm mexpected
    = do expected <- maybe (do nm <- genName "delayTy"
                               u <- uniVar fc
                               ty <- metaVar fc erased env nm (TType fc u)
                               nf env ty)
                           pure mexpected
         let solvemode = case elabMode elabinfo of
                              InLHS c => inLHS
                              _ => inTerm
         solveConstraints solvemode Normal
         -- Can only check if we know the expected type already because we
         -- need to infer the delay reason
         delayOnFailure fc rig env (Just expected) delayError LazyDelay
            (\delayed =>
                do expected <- ifThenElse delayed
                                 (do exp <- quote env expected
                                     nf env exp)
                                 (pure expected)
                   case !(expand expected) of
                      VDelayed _ r expnf =>
                         do defs <- get Ctxt
                            (tm', gty) <- check rig elabinfo nest env tm
                                                (Just expnf)
                            ty <- quote env gty
                            pure (TDelay fc r ty tm',
                                  VDelayed fc r gty)
                      ty => do logNF "elab.delay" 5 "Expected delay type" env ty
                               throw (GenericMsg fc ("Can't infer delay type")))
  where
    delayError : Error -> Bool
    delayError (GenericMsg {}) = True
    delayError _ = False

export
checkForce : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             RigCount -> ElabInfo ->
             NestedNames vars -> Env Term vars ->
             FC -> RawImp -> Maybe (Glued vars) ->
             Core (Term vars, Glued vars)
checkForce rig elabinfo nest env fc tm exp
    = do defs <- get Ctxt
         let expf = maybe Nothing
                       (\gty => Just (VDelayed fc LUnknown gty))
                       exp
         (tm', gty) <- check rig elabinfo nest env tm expf
         tynf <- expand gty
         case tynf of
              VDelayed _ r expnf =>
                 pure (TForce fc r tm', expnf)
              _ => throw (GenericMsg fc "Forcing a non-delayed type")
