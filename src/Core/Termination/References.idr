module Core.Termination.References

import Core.Context
import Core.Context.Log

import Libraries.Data.NameMap

-- Check that the names a function refers to are terminating
export
totRefs : {auto c : Ref Ctxt Defs} ->
          Defs -> List Name -> Core Terminating
totRefs defs [] = pure IsTerminating
totRefs defs (n :: ns)
    = do rest <- totRefs defs ns
         Just d <- lookupCtxtExact n (gamma defs)
              | Nothing => pure rest
         case isTerminating (totality d) of
              IsTerminating => pure rest
              Unchecked => do
                logC "totality" 20 $ do pure $ "Totality unchecked for " ++ show !(toFullNames n)
                pure rest
              _ => case rest of
                          NotTerminating (BadCall ns)
                             => toFullNames $ NotTerminating (BadCall (n :: ns))
                          _ => toFullNames $ NotTerminating (BadCall [n])

export
totRefsIn : {auto c : Ref Ctxt Defs} ->
            Defs -> Term vars -> Core Terminating
totRefsIn defs ty = totRefs defs (keys (getRefs (Resolved (-1)) ty))
