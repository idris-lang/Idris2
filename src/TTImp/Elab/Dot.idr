module TTImp.Elab.Dot

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.ImplicitBind
import TTImp.TTImp

import Data.NameMap

%default covering

export
checkDot : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC -> DotReason -> RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
checkDot rig elabinfo nest env fc reason tm Nothing
    = throw (GenericMsg fc ("Dot pattern not valid here (unknown type) "
                            ++ show tm))
checkDot rig elabinfo nest env fc reason tm (Just gexpty)
    = case elabMode elabinfo of
        InLHS _ =>
          do (wantedTm, wantedTy) <- check rig
                                              (record { elabMode = InExpr }
                                                  elabinfo)
                                              nest env
                                              tm (Just gexpty)
             nm <- genName "dotTm"
             expty <- getTerm gexpty
             metaval <- metaVar fc rig env nm expty
             addDot fc env nm wantedTm reason metaval
             pure (metaval, gexpty)
        _ => throw (GenericMsg fc ("Dot pattern not valid here (Not LHS) "
                                   ++ show tm))

