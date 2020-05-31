module TTImp.Elab.RunElab

import Core.Context
import Core.Core
import Core.Env
import Core.GetType
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Reflect
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Reflect
import TTImp.TTImp

elabScript : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             FC -> RigCount -> ElabInfo -> NestedNames vars ->
             Env Term vars -> NF vars -> Maybe (Glued vars) ->
             Core (Term vars, Glued vars)
elabScript fc rig elabinfo nest env
           tm@(NDCon _ nm _ _ args) exp
    = do defs <- get Ctxt
         fnm <- toFullNames nm
         case fnm of
              NS ["Reflection", "Language"] (UN n)
                 => elabCon defs n args
              _ => failWith defs
  where
    failWith : Defs -> Core a
    failWith defs
      = do defs <- get Ctxt
           empty <- clearDefs defs
           throw (BadRunElab fc env !(quote empty env tm))

    elabCon : Defs -> String -> List (Closure vars) -> Core (Term vars, Glued vars)
    elabCon defs "Check" [ttimp]
        = do tt <- evalClosure defs ttimp
             raw <- reify defs tt
             check rig elabinfo nest env raw exp
    elabCon defs n args = failWith defs
elabScript fc rig elabinfo nest env script exp
    = do defs <- get Ctxt
         empty <- clearDefs defs
         throw (BadRunElab fc env !(quote empty env script))

export
checkRunElab : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars -> 
               FC -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRunElab rig elabinfo nest env fc script exp
    = do defs <- get Ctxt
         when (not (isExtension ElabReflection defs)) $
             throw (GenericMsg fc "%language ElabReflection not enabled")
         (stm, sty) <- check rig elabinfo nest env script Nothing
         elabScript fc rig elabinfo nest env !(nf defs env stm) exp
