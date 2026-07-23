module TTImp.ProcessRunElab

import Core.Env
import Core.Metadata
import Core.Reflect
import Core.UnifyState
import Core.Evaluate.Value
import Core.Evaluate.Normalise
import Core.Evaluate.Expand

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.RunElab
import TTImp.TTImp

%default covering

export
processRunElab : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
                 RawImp -> Core ()
processRunElab eopts nest env fc tm
    = do defs <- get Ctxt
         unless (isExtension ElabReflection defs) $
             throw (GenericMsg fc "%language ElabReflection not enabled")
         tidx <- resolveName (UN $ Basic "[elaborator script]")
         let n = NS reflectionNS (UN $ Basic "Elab")
         unit <- getCon fc defs (builtin "Unit")
         exp <- appConTop fc defs n [unit]

         stm <- checkTerm tidx InExpr eopts nest env tm !(nf env exp)
         ignore $ logTime 2 "Elaboration script" $
           elabScript top fc nest env !(expandFull !(nf env stm)) Nothing
