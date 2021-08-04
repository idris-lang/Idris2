module Compiler.Opts.InlineHeuristics

import Compiler.CompileExpr
import Core.Context
import Core.Context.Log
import Data.Vect

parameters (fn : Name)
    isVar : CExp vars -> Bool
    isVar (CLocal _ _) = True
    isVar (CRef _ _) = True
    isVar (CForce _ _ x) = isVar x
    isVar (CDelay _ _ x) = isVar x
    isVar _ = False

    simple : CExp vars -> Bool
    simple (CLocal _ _) = True
    simple (CRef _ _) = True
    simple (CLam _ _ _) = False
    simple (CLet _ _ _ _ _) = False
    simple (CApp _ (CRef _ fn') xs) = not (fn == fn') && all isVar xs
    simple (CApp _ fn xs) = isVar fn && all isVar xs
    simple (CCon _ _ _ _ xs) = all isVar xs
    simple (COp _ _ xs) = all isVar xs
    simple (CExtPrim _ _ xs) = all isVar xs
    simple (CForce _ _ y) = simple y
    simple (CDelay _ _ y) = simple y
    simple (CConCase _ _ _ _) = False
    simple (CConstCase _ _ _ _) = False
    simple (CPrimVal _ _) = True
    simple (CErased _) = True
    simple (CCrash _ _) = False

    inlineCDef : CDef -> Bool
    inlineCDef (MkFun args exp) =
        simple exp
    inlineCDef _ = False

export
inlineHeuristics : Ref Ctxt Defs => Name -> Core ()
inlineHeuristics fn = do
    defs <- get Ctxt
    Just (fnIdx, gdef) <- lookupCtxtExactI fn defs.gamma
        | Nothing => pure ()
    let Just cdef = gdef.compexpr
        | Nothing => pure ()
    let True = inlineCDef fn cdef
        | False => pure ()
    log "compiler.inline.heuristic" 25 $ "inlining heuristic decided to inline: " ++ show fn
    setFlag EmptyFC (Resolved fnIdx) Inline
