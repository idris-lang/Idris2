module Compiler.Identity

import Compiler.CompileExpr
import Core.Context
import Core.Context.Log

getArg : FC -> Nat -> (args : List Name) -> Maybe (CExp args)
getArg _ _ [] = Nothing
getArg fc Z (a :: _) = Just $ CLocal fc First
getArg fc (S k) (_ :: as) = weaken <$> getArg fc k as

idCDef : Nat -> CDef -> Maybe CDef
idCDef idx (MkFun args exp) = MkFun args <$> getArg (getFC exp) idx args
idCDef _ def = Just def

export
setIdentity : Ref Ctxt Defs => Name -> Core ()
setIdentity fn = do
    log "compiler.identity" 10 $ "processing identity flag for: " ++ show fn
    defs <- get Ctxt
    Just gdef <- lookupCtxtExact fn defs.gamma
        | Nothing => pure ()
    log "compiler.identity" 25 $ "flags for " ++ show fn ++ ": " ++ show gdef.flags
    let Just flg@(Identity idx) = find isId gdef.flags
        | _ => pure ()
    log "compiler.identity" 5 $ "found identity flag for: " ++ show fn ++ ", " ++ show idx
                             ++ "\n\told def: " ++ show gdef.compexpr
    let Just cdef = the _ $ gdef.compexpr >>= idCDef idx
        | Nothing => pure ()
    log "compiler.identity" 15 $ "new def: " ++ show cdef
    unsetFlag EmptyFC fn flg -- other optimisations might mess with argument counts
    setCompiled fn cdef
  where
    isId : DefFlag -> Bool
    isId (Identity _) = True
    isId _ = False
