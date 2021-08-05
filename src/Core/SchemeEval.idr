module Core.SchemeEval

-- Top level interface to the scheme based evaluator
-- Drops back to the default slow evaluator if scheme isn't available

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Normalise
import Core.SchemeEval.Compile
import Core.SchemeEval.Evaluate
import Core.SchemeEval.ToScheme
import Core.TT

import Libraries.Data.NameMap
import Libraries.Utils.Scheme

snormaliseMode : {auto c : Ref Ctxt Defs} ->
                 {vars : _} ->
                 SchemeMode -> Env Term vars -> Term vars -> Core (Term vars)
snormaliseMode mode env tm
    = do defs <- get Ctxt
         True <- initialiseSchemeEval
             | _ => normalise defs env tm
         sval <- seval mode env tm
         quote sval

export
snormalise : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Env Term vars -> Term vars -> Core (Term vars)
snormalise = snormaliseMode BlockExport

export
snormaliseAll : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Env Term vars -> Term vars -> Core (Term vars)
snormaliseAll = snormaliseMode EvalAll
