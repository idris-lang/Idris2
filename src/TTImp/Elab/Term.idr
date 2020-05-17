module TTImp.Elab.Term

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Options
-- import Core.Reflect
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Ambiguity
import TTImp.Elab.App
import TTImp.Elab.As
import TTImp.Elab.Binders
import TTImp.Elab.Case
import TTImp.Elab.Check
import TTImp.Elab.Dot
import TTImp.Elab.Hole
import TTImp.Elab.ImplicitBind
import TTImp.Elab.Lazy
import TTImp.Elab.Local
import TTImp.Elab.Prim
-- import TTImp.Elab.Quote
import TTImp.Elab.Record
import TTImp.Elab.Rewrite
-- import TTImp.Reflect
import TTImp.TTImp

%default covering

-- If the expected type has an implicit pi, elaborate with leading
-- implicit lambdas if they aren't there already.
insertImpLam : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               Env Term vars ->
               (term : RawImp) -> (expected : Maybe (Glued vars)) ->
               Core RawImp
insertImpLam {vars} env tm (Just ty) = bindLam tm ty
  where
    -- If we can decide whether we need implicit lambdas without looking
    -- at the normal form, do so
    bindLamTm : RawImp -> Term vs -> Core (Maybe RawImp)
    bindLamTm tm@(ILam _ _ Implicit _ _ _) (Bind fc n (Pi _ Implicit _) sc)
        = pure (Just tm)
    bindLamTm tm@(ILam _ _ AutoImplicit _ _ _) (Bind fc n (Pi _ AutoImplicit _) sc)
        = pure (Just tm)
    bindLamTm tm (Bind fc n (Pi c Implicit ty) sc)
        = do n' <- genVarName (nameRoot n)
             Just sc' <- bindLamTm tm sc
                 | Nothing => pure Nothing
             pure $ Just (ILam fc c Implicit (Just n') (Implicit fc False) sc')
    bindLamTm tm (Bind fc n (Pi c AutoImplicit ty) sc)
        = do n' <- genVarName (nameRoot n)
             Just sc' <- bindLamTm tm sc
                 | Nothing => pure Nothing
             pure $ Just (ILam fc c AutoImplicit (Just n') (Implicit fc False) sc')
    bindLamTm tm exp
        = case getFn exp of
               Ref _ Func _ => pure Nothing -- might still be implicit
               TForce _ _ _ => pure Nothing
               Bind _ _ (Lam _ _ _) _ => pure Nothing
               _ => pure $ Just tm

    bindLamNF : RawImp -> NF vars -> Core RawImp
    bindLamNF tm@(ILam _ _ Implicit _ _ _) (NBind fc n (Pi _ Implicit _) sc)
        = pure tm
    bindLamNF tm@(ILam _ _ AutoImplicit _ _ _) (NBind fc n (Pi _ AutoImplicit _) sc)
        = pure tm
    bindLamNF tm (NBind fc n (Pi c Implicit ty) sc)
        = do defs <- get Ctxt
             n' <- genVarName (nameRoot n)
             sctm <- sc defs (toClosure defaultOpts env (Ref fc Bound n'))
             sc' <- bindLamNF tm sctm
             pure $ ILam fc c Implicit (Just n') (Implicit fc False) sc'
    bindLamNF tm (NBind fc n (Pi c AutoImplicit ty) sc)
        = do defs <- get Ctxt
             n' <- genVarName (nameRoot n)
             sctm <- sc defs (toClosure defaultOpts env (Ref fc Bound n'))
             sc' <- bindLamNF tm sctm
             pure $ ILam fc c AutoImplicit (Just n') (Implicit fc False) sc'
    bindLamNF tm sc = pure tm

    bindLam : RawImp -> Glued vars -> Core RawImp
    bindLam tm gty
        = do ty <- getTerm gty
             Just tm' <- bindLamTm tm ty
                | Nothing =>
                    do nf <- getNF gty
                       bindLamNF tm nf
             pure tm'
insertImpLam env tm _ = pure tm

-- Main driver for checking terms, after implicits have been added.
-- Implements 'checkImp' in TTImp.Elab.Check
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo ->
            NestedNames vars -> Env Term vars -> RawImp -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkTerm rig elabinfo nest env (IVar fc n) exp
    = -- It may actually turn out to be an application, if the expected
      -- type is expecting an implicit argument, so check it as an
      -- application with no arguments
      checkApp rig elabinfo nest env fc (IVar fc n) [] [] exp
checkTerm rig elabinfo nest env (IPi fc r p (Just n) argTy retTy) exp
    = checkPi rig elabinfo nest env fc r p n argTy retTy exp
checkTerm rig elabinfo nest env (IPi fc r p Nothing argTy retTy) exp
    = do n <- case p of
                   Explicit => genVarName "arg"
                   Implicit => genVarName "impArg"
                   AutoImplicit => genVarName "conArg"
         checkPi rig elabinfo nest env fc r p n argTy retTy exp
checkTerm rig elabinfo nest env (ILam fc r p (Just n) argTy scope) exp
    = checkLambda rig elabinfo nest env fc r p n argTy scope exp
checkTerm rig elabinfo nest env (ILam fc r p Nothing argTy scope) exp
    = do n <- genVarName "_"
         checkLambda rig elabinfo nest env fc r p n argTy scope exp
checkTerm rig elabinfo nest env (ILet fc r n nTy nVal scope) exp
    = checkLet rig elabinfo nest env fc r n nTy nVal scope exp
checkTerm rig elabinfo nest env (ICase fc scr scrty alts) exp
    = checkCase rig elabinfo nest env fc scr scrty alts exp
checkTerm rig elabinfo nest env (ILocal fc nested scope) exp
    = checkLocal rig elabinfo nest env fc nested scope exp
checkTerm rig elabinfo nest env (ICaseLocal fc uname iname args scope) exp
    = checkCaseLocal rig elabinfo nest env fc uname iname args scope exp
checkTerm rig elabinfo nest env (IUpdate fc upds rec) exp
    = checkUpdate rig elabinfo nest env fc upds rec exp
checkTerm rig elabinfo nest env (IApp fc fn arg) exp
    = checkApp rig elabinfo nest env fc fn [arg] [] exp
checkTerm rig elabinfo nest env (IWithApp fc fn arg) exp
    = throw (GenericMsg fc "with application not implemented yet")
checkTerm rig elabinfo nest env (IImplicitApp fc fn nm arg) exp
    = checkApp rig elabinfo nest env fc fn [] [(nm, arg)] exp
checkTerm rig elabinfo nest env (ISearch fc depth) (Just gexpty)
    = do est <- get EST
         nm <- genName "search"
         expty <- getTerm gexpty
         sval <- searchVar fc rig depth (Resolved (defining est)) env nm expty
         pure (sval, gexpty)
checkTerm rig elabinfo nest env (ISearch fc depth) Nothing
    = do est <- get EST
         nmty <- genName "searchTy"
         ty <- metaVar fc erased env nmty (TType fc)
         nm <- genName "search"
         sval <- searchVar fc rig depth (Resolved (defining est)) env nm ty
         pure (sval, gnf env ty)
checkTerm rig elabinfo nest env (IAlternative fc uniq alts) exp
    = checkAlternative rig elabinfo nest env fc uniq alts exp
checkTerm rig elabinfo nest env (IRewrite fc rule tm) exp
    = checkRewrite rig elabinfo nest env fc rule tm exp
checkTerm rig elabinfo nest env (ICoerced fc tm) exp
    = checkTerm rig elabinfo nest env tm exp
checkTerm rig elabinfo nest env (IBindHere fc binder sc) exp
    = checkBindHere rig elabinfo nest env fc binder sc exp
checkTerm rig elabinfo nest env (IBindVar fc n) exp
    = checkBindVar rig elabinfo nest env fc n exp
checkTerm rig elabinfo nest env (IAs fc side n_in tm) exp
    = checkAs rig elabinfo nest env fc side n_in tm exp
checkTerm rig elabinfo nest env (IMustUnify fc reason tm) exp
    = checkDot rig elabinfo nest env fc reason tm exp
checkTerm rig elabinfo nest env (IDelayed fc r tm) exp
    = checkDelayed rig elabinfo nest env fc r tm exp
checkTerm rig elabinfo nest env (IDelay fc tm) exp
    = checkDelay rig elabinfo nest env fc tm exp
checkTerm rig elabinfo nest env (IForce fc tm) exp
    = checkForce rig elabinfo nest env fc tm exp
checkTerm rig elabinfo nest env (IQuote fc tm) exp
    = throw (GenericMsg fc "Reflection not implemented yet")
--     = checkQuote rig elabinfo nest env fc tm exp
checkTerm rig elabinfo nest env (IQuoteDecl fc tm) exp
    = throw (GenericMsg fc "Declaration reflection not implemented yet")
checkTerm rig elabinfo nest env (IUnquote fc tm) exp
    = throw (GenericMsg fc "Can't escape outside a quoted term")
checkTerm rig elabinfo nest env (IRunElab fc tm) exp
    = throw (GenericMsg fc "RunElab not implemented yet")
checkTerm {vars} rig elabinfo nest env (IPrimVal fc c) exp
    = do let (cval, cty) = checkPrim {vars} fc c
         checkExp rig elabinfo env fc cval (gnf env cty) exp
checkTerm rig elabinfo nest env (IType fc) exp
    = checkExp rig elabinfo env fc (TType fc) (gType fc) exp

checkTerm rig elabinfo nest env (IHole fc str) exp
    = checkHole rig elabinfo nest env fc str exp
checkTerm rig elabinfo nest env (IUnifyLog fc n tm) exp
    = do opts <- getSession
         let lvl = logLevel opts
         setLogLevel n
         r <- check rig elabinfo nest env tm exp
         setLogLevel lvl
         pure r
checkTerm rig elabinfo nest env (Implicit fc b) (Just gexpty)
    = do nm <- genName "_"
         expty <- getTerm gexpty
         metaval <- metaVar fc rig env nm expty
         -- Add to 'bindIfUnsolved' if 'b' set
         when (b && bindingVars elabinfo) $
            do est <- get EST
               expty <- getTerm gexpty
               -- Explicit because it's an explicitly given thing!
               put EST (addBindIfUnsolved nm rig Explicit env metaval expty est)
         pure (metaval, gexpty)
checkTerm rig elabinfo nest env (Implicit fc b) Nothing
    = do nmty <- genName "implicit_type"
         ty <- metaVar fc erased env nmty (TType fc)
         nm <- genName "_"
         metaval <- metaVar fc rig env nm ty
         -- Add to 'bindIfUnsolved' if 'b' set
         when (b && bindingVars elabinfo) $
            do est <- get EST
               put EST (addBindIfUnsolved nm rig Explicit env metaval ty est)
         pure (metaval, gnf env ty)

-- Declared in TTImp.Elab.Check
-- check : {vars : _} ->
--         {auto c : Ref Ctxt Defs} ->
--         {auto m : Ref MD Metadata} ->
--         {auto u : Ref UST UState} ->
--         {auto e : Ref EST (EState vars)} ->
--         RigCount -> ElabInfo -> Env Term vars -> RawImp ->
--         Maybe (Glued vars) ->
--         Core (Term vars, Glued vars)
-- If we've just inserted an implicit coercion (in practice, that's either
-- a force or delay) then check the term with any further insertions
TTImp.Elab.Check.check rigc elabinfo nest env (ICoerced fc tm) exp
    = checkImp rigc elabinfo nest env tm exp
-- Don't add implicits/coercions on local blocks or record updates
TTImp.Elab.Check.check rigc elabinfo nest env tm@(ILet fc c n nty nval sc) exp
    = checkImp rigc elabinfo nest env tm exp
TTImp.Elab.Check.check rigc elabinfo nest env tm@(ILocal fc ds sc) exp
    = checkImp rigc elabinfo nest env tm exp
TTImp.Elab.Check.check rigc elabinfo nest env tm@(IUpdate fc fs rec) exp
    = checkImp rigc elabinfo nest env tm exp
TTImp.Elab.Check.check rigc elabinfo nest env tm_in exp
    = do defs <- get Ctxt
         est <- get EST
         tm <- expandAmbigName (elabMode elabinfo) nest env tm_in [] tm_in exp
         case elabMode elabinfo of
              InLHS _ => -- Don't expand implicit lambda on lhs
                 checkImp rigc elabinfo nest env tm exp
              _ => do tm' <- insertImpLam env tm exp
                      checkImp rigc elabinfo nest env tm' exp

-- As above, but doesn't add any implicit lambdas, forces, delays, etc
-- checkImp : {vars : _} ->
--            {auto c : Ref Ctxt Defs} ->
--            {auto m : Ref MD Metadata} ->
--            {auto u : Ref UST UState} ->
--            {auto e : Ref EST (EState vars)} ->
--            RigCount -> ElabInfo -> Env Term vars -> RawImp -> Maybe (Glued vars) ->
--            Core (Term vars, Glued vars)
TTImp.Elab.Check.checkImp rigc elabinfo nest env tm exp
    = checkTerm rigc elabinfo nest env tm exp

