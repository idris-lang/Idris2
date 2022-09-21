module TTImp.Elab.As

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.ImplicitBind
import TTImp.TTImp

import Data.List

%default covering

export
checkAs : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          RigCount -> ElabInfo ->
          NestedNames vars -> Env Term vars ->
          FC -> (nameFC : FC) -> UseSide -> Name -> RawImp -> Maybe (Glued vars) ->
          Core (Term vars, Glued vars)
checkAs rig elabinfo nest env fc nameFC side n_in pat topexp
    = do let elabmode = elabMode elabinfo
         let InLHS _ = elabmode
             | _ => do log "elab.as" 2 $ "Bad @-pattern " ++ show pat
                       throw (GenericMsg fc "@-patterns only allowed in pattern clauses")
         est <- get EST
         let n = PV n_in (defining est)
         noteLHSPatVar elabmode n_in
         notePatVar n
         case lookup n (boundNames est) of
              Nothing =>
                 do (pattm, patty) <- check rigPat elabinfo nest env pat topexp
                    (tm, exp, bty) <- mkPatternHole nameFC rig n env
                                            (implicitMode elabinfo)
                                            topexp
                    log "elab.as" 5 $ "Added as pattern name " ++ show (n, (rigAs, tm, exp, bty))
                    defs <- get Ctxt
                    update EST { boundNames $= ((n, AsBinding rigAs Explicit tm exp pattm) :: ),
                                 toBind $= ((n, AsBinding rigAs Explicit tm bty pattm) ::) }
                    (ntm, nty) <- checkExp rig elabinfo env nameFC tm (gnf env exp)
                                           (Just patty)

                    -- Add the name type to the metadata
                    log "metadata.names" 7 $ "checkAs is adding ↓"
                    addNameType nameFC n_in env !(getTerm nty)

                    pure (As fc side ntm pattm, patty)
              Just bty => throw (NonLinearPattern fc n_in)
  where
    -- Only one side can be usable if it's linear! Normally we'd assume this
    -- to be the new variable (UseRight), but in generated case blocks it's
    -- better if it's the pattern (UseLeft)
    rigPat' : UseSide -> RigCount
    rigPat' UseLeft = if isLinear rig then linear else rig
    rigPat' UseRight = if isLinear rig then erased else rig

    rigPat : RigCount
    rigPat = rigPat' side

    rigAs' : UseSide -> RigCount
    rigAs' UseLeft = if isLinear rig then erased else rig
    rigAs' UseRight = if isLinear rig then linear else rig

    rigAs : RigCount
    rigAs = rigAs' side
