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
    -- We can't determine based on heuristics that something should be inlined unless
    -- it is publicly exported because we may be crossing module boundaries and changes
    -- to the given def will not modify the source module's interface hash so you can get
    -- stuck with an old def inlined into the destination module. This is only a problem
    -- when determining to inline based on heuristics, though -- if the definition was
    -- explicitly marked for inlining by the programmer, it will be inlined without any
    -- intervention by this function.
    -- We could lift this public restriction if we checked that the source def was _either
    -- public OR the destination was the same module as the source_.
    let Public = gdef.visibility
        | _ => pure ()
    unless (NoInline `elem` gdef.flags) $ do
      log "compiler.inline.heuristic" 25 $ "inlining heuristic decided to inline: " ++ show fn
      setFlag EmptyFC (Resolved fnIdx) Inline
