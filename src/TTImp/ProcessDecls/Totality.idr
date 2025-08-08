module TTImp.ProcessDecls.Totality

import Core.Context
import Core.Context.Log
import Core.Termination

import Libraries.Data.NameMap

%default covering

export
checkTotalityOK : {auto c : Ref Ctxt Defs} ->
                  Name -> Core (Maybe Error)
checkTotalityOK (NS _ (MN _ _)) = pure Nothing -- not interested in generated names
checkTotalityOK (NS _ (CaseBlock _ _)) = pure Nothing -- case blocks checked elsewhere
checkTotalityOK n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure Nothing
         let fc = location gdef

         let treq = fromMaybe !getDefaultTotalityOption (findSetTotal (flags gdef))

         -- #524: need to check positivity even if we're not in a total context
         -- because a definition coming later may need to know it is positive
         case definition gdef of
           (TCon _ _ _ _ _ _ _) => ignore $ checkPositive fc n
           _ => pure ()

         -- Once that is done, we build up errors if necessary
         let tot = totality gdef
         log "totality" 3 $ show n ++ " must be: " ++ show treq
         case treq of
            PartialOK => pure Nothing
            CoveringOnly => checkCovering fc (isCovering tot)
            Total => checkTotality fc
  where
    checkCovering : FC -> Covering -> Core (Maybe Error)
    checkCovering fc IsCovering = pure Nothing
    checkCovering fc cov
        = pure (Just (NotCovering fc n cov))

    checkTotality : FC -> Core (Maybe Error)
    checkTotality fc
        = do ignore $ logTime 3 ("Checking Termination " ++ show n) (checkTotal fc n)
             -- ^ checked lazily, so better calculate here
             t <- getTotality fc n
             err <- checkCovering fc (isCovering t)
             maybe (case isTerminating t of
                         NotTerminating p => pure (Just (NotTotal fc n p))
                         _ => pure Nothing)
                   (pure . Just) err

-- Check totality of all the names added in the file, and return a list of
-- totality errors.
-- Do this at the end of processing a file (or a batch of definitions) since
-- they might be mutually dependent so we need all the definitions to be able
-- to check accurately.
export
getTotalityErrors : {auto c : Ref Ctxt Defs} ->
                    Core (List Error)
getTotalityErrors
    = do defs <- get Ctxt
         errs <- traverse checkTotalityOK (keys (toSave defs))
         pure (mapMaybe id errs)
