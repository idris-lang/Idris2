module Core.Error

import Core.Core
import Core.Context

export
tryError : {auto c : Ref Ctxt Defs} ->
           {auto refs : RefList ls} ->
           Core a -> Core (Either Error a)
tryError elab
    = do val <- getAll refs
         defs <- branch
         catch (do res <- elab
                   commit
                   pure (Right res))
               (\err => do putAll refs val
                           defs' <- get Ctxt
                           put Ctxt (record { timings = timings defs' } defs)
                           pure (Left err))

export
try : {auto c : Ref Ctxt Defs} ->
      {auto refs : RefList ls} ->
      Core a -> Core a -> Core a
try elab1 elab2
    = do Right ok <- tryError {refs} elab1
               | Left err => elab2
         pure ok

export
handle : {auto c : Ref Ctxt Defs} ->
         {auto refs : RefList ls} ->
         Core a -> (Error -> Core a) -> Core a
handle elab1 elab2
    = do Right ok <- tryError {refs} elab1
               | Left err => elab2 err
         pure ok

export
tryCatchFinally : {auto c : Ref Ctxt Defs}
               -> {auto refs : RefList ls}
               -> (try : Core ())
               -> (catch : Error -> Core ())
               -> (finally : Core ())
               -> Core ()
tryCatchFinally try catch finally
    = do Right _ <- tryError {refs} try
               | Left err => do
                   Right _ <- tryError {refs} (catch err)
                     | Left err => do finally; throw err
                   finally

         finally
