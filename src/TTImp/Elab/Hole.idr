module TTImp.Elab.Hole

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.TTImp

%default covering

export
checkHole : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo ->
            NestedNames vars -> Env Term vars ->
            FC -> String -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkHole rig elabinfo nest env fc n_in (Just gexpty)
    = do nm <- inCurrentNS (UN n_in)
         defs <- get Ctxt
         Nothing <- lookupCtxtExact nm (gamma defs)
             | _ => do log 1 $ show nm ++ " already defined"
                       throw (AlreadyDefined fc nm)
         expty <- getTerm gexpty
         -- Turn lets into lambda before making the hole so that they
         -- get abstracted over in the hole (it's fine here, unlike other
         -- holes, because we're not trying to unify it so it's okay if
         -- applying the metavariable isn't a pattern form)
         let env' = letToLam env
         (idx, metaval) <- metaVarI fc rig env' nm expty
         -- Record the LHS for this hole in the metadata
         withCurrentLHS (Resolved idx)
         addUserHole nm
         saveHole nm
         pure (metaval, gexpty)
checkHole rig elabinfo nest env fc n_in exp
    = do nmty <- genName ("type_of_" ++ n_in)
         let env' = letToLam env
         ty <- metaVar fc erased env' nmty (TType fc)
         nm <- inCurrentNS (UN n_in)
         defs <- get Ctxt
         Nothing <- lookupCtxtExact nm (gamma defs)
             | _ => do log 1 $ show nm ++ " already defined"
                       throw (AlreadyDefined fc nm)
         (idx, metaval) <- metaVarI fc rig env' nm ty
         withCurrentLHS (Resolved idx)
         addUserHole nm
         saveHole nm
         pure (metaval, gnf env ty)
