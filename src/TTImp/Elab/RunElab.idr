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
import TTImp.Unelab

elabScript : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             FC -> ElabInfo -> NestedNames vars ->
             Env Term vars -> NF vars -> Maybe (Glued vars) ->
             Core (NF vars)
elabScript fc elabinfo nest env (NDCon nfc nm t ar args) exp
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
           throw (BadRunElab fc env !(quote empty env (NDCon nfc nm t ar args)))

    scriptRet : Reflect a => a -> Core (NF vars)
    scriptRet tm
        = do defs <- get Ctxt
             nfOpts withAll defs env !(reflect fc defs env tm)

    elabCon : Defs -> String -> List (Closure vars) -> Core (NF vars)
    elabCon defs "Pure" [_,val] = evalClosure defs val
    elabCon defs "Bind" [_,_,act,k]
        = do act' <- elabScript fc elabinfo nest env
                                !(evalClosure defs act) exp
             case !(evalClosure defs k) of
                  NBind _ x (Lam _ _ _) sc =>
                      elabScript fc elabinfo nest env
                                 !(sc defs (toClosure withAll env
                                                 !(quote defs env act'))) exp
                  _ => failWith defs
    elabCon defs "LogMsg" [lvl, str]
        = do lvl' <- evalClosure defs lvl
             logC !(reify defs lvl') $
                  do str' <- evalClosure defs str
                     reify defs str'
             scriptRet ()
    elabCon defs "LogTerm" [lvl, str, tm]
        = do lvl' <- evalClosure defs lvl
             logC !(reify defs lvl') $
                  do str' <- evalClosure defs str
                     tm' <- evalClosure defs tm
                     pure $ !(reify defs str') ++ ": " ++
                             show (the RawImp !(reify defs tm'))
             scriptRet ()
    elabCon defs "Check" [ttimp] = evalClosure defs ttimp -- to be reified
    elabCon defs "Goal" []
        = do let Just gty = exp
                 | Nothing => nfOpts withAll defs env
                                     !(reflect fc defs env (the (Maybe RawImp) Nothing))
             ty <- getTerm gty
             scriptRet (Just !(unelabNoSugar env ty))
    elabCon defs n args = failWith defs
elabScript fc elabinfo nest env script exp
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
         (stm, sty) <- runDelays 0 $
                           check rig elabinfo nest env script Nothing
         defs <- get Ctxt -- checking might have resolved some holes
         ntm <- elabScript fc elabinfo nest env
                           !(nfOpts withAll defs env stm) exp
         defs <- get Ctxt -- might have updated as part of the script
         check rig elabinfo nest env !(reify defs ntm) exp
