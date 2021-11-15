module TTImp.Elab.RunElab

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Reflect
import Core.Unify
import Core.TT
import Core.Value

import Idris.Syntax
import Idris.Resugar

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Reflect
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Unelab

%default covering

record NameInfo where
  constructor MkNameInfo
  nametype : NameType

lookupNameInfo : Name -> Context -> Core (List (Name, NameInfo))
lookupNameInfo n ctxt
    = do res <- lookupCtxtName n ctxt
         pure (map (\ (n, i, gd) =>
                      (n, MkNameInfo { nametype = getNameType (definition gd) } ))
                   res)
  where
    getNameType : Def -> NameType
    getNameType (DCon t a _) = DataCon t a
    getNameType (TCon t a _ _ _ _ _ _) = TyCon t a
    getNameType _ = Func

Reflect NameInfo where
  reflect fc defs lhs env inf
      = do nt <- reflect fc defs lhs env (nametype inf)
           appCon fc defs (reflectiontt "MkNameInfo") [nt]

export
elabScript : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Syn SyntaxInfo} ->
             FC -> NestedNames vars ->
             Env Term vars -> NF vars -> Maybe (Glued vars) ->
             Core (NF vars)
elabScript fc nest env script@(NDCon nfc nm t ar args) exp
    = do defs <- get Ctxt
         fnm <- toFullNames nm
         case fnm of
              NS ns (UN (Basic n))
                 => if ns == reflectionNS
                      then elabCon defs n (map snd args)
                      else failWith defs $ "bad reflection namespace " ++ show ns
              _ => failWith defs $ "bad fullnames " ++ show fnm
  where
    failWith : Defs -> String -> Core a
    failWith defs desc
      = do empty <- clearDefs defs
           throw (BadRunElab fc env !(quote empty env script) desc)

    scriptRet : Reflect a => a -> Core (NF vars)
    scriptRet tm
        = do defs <- get Ctxt
             nfOpts withAll defs env !(reflect fc defs False env tm)

    elabCon : Defs -> String -> List (Closure vars) -> Core (NF vars)
    elabCon defs "Pure" [_,val]
        = do empty <- clearDefs defs
             evalClosure empty val
    elabCon defs "Bind" [_,_,act,k]
        = do act' <- elabScript fc nest env
                                !(evalClosure defs act) exp
             case !(evalClosure defs k) of
                  NBind _ x (Lam _ _ _ _) sc =>
                      elabScript fc nest env
                              !(sc defs (toClosure withAll env
                                              !(quote defs env act'))) exp
                  x => failWith defs $ "non-function RHS of a Bind: " ++ show x
    elabCon defs "Fail" [_, mbfc, msg]
        = do msg' <- evalClosure defs msg
             let customFC = case !(evalClosure defs mbfc >>= reify defs) of
                               EmptyFC => fc
                               x       => x
             throw (GenericMsg customFC ("Error during reflection: " ++
                                      !(reify defs msg')))
    elabCon defs "Try" [_, elab1, elab2]
        = tryUnify (elabScript fc nest env !(evalClosure defs elab1) exp)
                   (elabScript fc nest env !(evalClosure defs elab2) exp)
    elabCon defs "LogMsg" [topic, verb, str]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     reify defs str'
             scriptRet ()
    elabCon defs "LogTerm" [topic, verb, str, tm]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     tm' <- evalClosure defs tm
                     pure $ !(reify defs str') ++ ": " ++
                             show (the RawImp !(reify defs tm'))
             scriptRet ()
    elabCon defs "LogSugaredTerm" [topic, verb, str, tm]
        = do topic' <- evalClosure defs topic
             verb' <- evalClosure defs verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- evalClosure defs str
                     tm' <- reify defs !(evalClosure defs tm)
                     ptm <- pterm (map defaultKindedName tm')
                     pure $ !(reify defs str') ++ ": " ++ show ptm
             scriptRet ()
    elabCon defs "Check" [exp, ttimp]
        = do exp' <- evalClosure defs exp
             ttimp' <- evalClosure defs ttimp
             tidx <- resolveName (UN $ Basic "[elaborator script]")
             e <- newRef EST (initEState tidx env)
             (checktm, _) <- runDelays (const True) $
                     check top (initElabInfo InExpr) nest env !(reify defs ttimp')
                           (Just (glueBack defs env exp'))
             empty <- clearDefs defs
             nf empty env checktm
    elabCon defs "Quote" [exp, tm]
        = do tm' <- evalClosure defs tm
             defs <- get Ctxt
             empty <- clearDefs defs
             scriptRet $ map rawName !(unelabUniqueBinders env !(quote empty env tm'))
    elabCon defs "Lambda" [x, _, scope]
        = do empty <- clearDefs defs
             NBind bfc x (Lam fc' c p ty) sc <- evalClosure defs scope
                   | _ => throw (GenericMsg fc "Not a lambda")
             n <- genVarName "x"
             sc' <- sc defs (toClosure withAll env (Ref bfc Bound n))
             qsc <- quote empty env sc'
             let lamsc = refToLocal n x qsc
             qp <- quotePi p
             qty <- quote empty env ty
             let env' = Lam fc' c qp qty :: env

             runsc <- elabScript fc (weaken nest) env'
                                 !(nf defs env' lamsc) Nothing -- (map weaken exp)
             nf empty env (Bind bfc x (Lam fc' c qp qty) !(quote empty env' runsc))
       where
         quotePi : PiInfo (Closure vars) -> Core (PiInfo (Term vars))
         quotePi Explicit = pure Explicit
         quotePi Implicit = pure Implicit
         quotePi AutoImplicit = pure AutoImplicit
         quotePi (DefImplicit t) = throw (GenericMsg fc "Can't add default lambda")
    elabCon defs "Goal" []
        = do let Just gty = exp
                 | Nothing => nfOpts withAll defs env
                                     !(reflect fc defs False env (the (Maybe RawImp) Nothing))
             ty <- getTerm gty
             scriptRet (Just $ map rawName $ !(unelabUniqueBinders env ty))
    elabCon defs "LocalVars" []
        = scriptRet vars
    elabCon defs "GenSym" [str]
        = do str' <- evalClosure defs str
             n <- genVarName !(reify defs str')
             scriptRet n
    elabCon defs "InCurrentNS" [n]
        = do n' <- evalClosure defs n
             nsn <- inCurrentNS !(reify defs n')
             scriptRet nsn
    elabCon defs "GetType" [n]
        = do n' <- evalClosure defs n
             res <- lookupTyName !(reify defs n') (gamma defs)
             scriptRet !(traverse unelabType res)
      where
        unelabType : (Name, Int, ClosedTerm) -> Core (Name, RawImp)
        unelabType (n, _, ty)
            = pure (n, map rawName !(unelabUniqueBinders [] ty))
    elabCon defs "GetInfo" [n]
        = do n' <- evalClosure defs n
             res <- lookupNameInfo !(reify defs n') (gamma defs)
             scriptRet res
    elabCon defs "GetLocalType" [n]
        = do n' <- evalClosure defs n
             n <- reify defs n'
             case defined n env of
                  Just (MkIsDefined rigb lv) =>
                       do let binder = getBinder lv env
                          let bty = binderType binder
                          scriptRet $ map rawName !(unelabUniqueBinders env bty)
                  _ => throw (GenericMsg fc (show n ++ " is not a local variable"))
    elabCon defs "GetCons" [n]
        = do n' <- evalClosure defs n
             cn <- reify defs n'
             Just (TCon _ _ _ _ _ _ cons _) <-
                     lookupDefExact cn (gamma defs)
                 | _ => throw (GenericMsg fc (show cn ++ " is not a type"))
             scriptRet cons
    elabCon defs "Declare" [d]
        = do d' <- evalClosure defs d
             decls <- reify defs d'
             traverse_ (processDecl [] (MkNested []) []) decls
             scriptRet ()
    elabCon defs n args = failWith defs $ "unexpected Elab constructor " ++ n ++
                                          ", or incorrect count of arguments: " ++ show (length args)
elabScript fc nest env script exp
    = do defs <- get Ctxt
         empty <- clearDefs defs
         throw (BadRunElab fc env !(quote empty env script) "script is not a data value")

export
checkRunElab : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRunElab rig elabinfo nest env fc script exp
    = do expected <- mkExpected exp
         defs <- get Ctxt
         unless (isExtension ElabReflection defs) $
             throw (GenericMsg fc "%language ElabReflection not enabled")
         let n = NS reflectionNS (UN $ Basic "Elab")
         let ttn = reflectiontt "TT"
         elabtt <- appCon fc defs n [expected]
         (stm, sty) <- runDelays (const True) $
                           check rig elabinfo nest env script (Just (gnf env elabtt))
         defs <- get Ctxt -- checking might have resolved some holes
         ntm <- elabScript fc nest env
                           !(nfOpts withAll defs env stm) (Just (gnf env expected))
         defs <- get Ctxt -- might have updated as part of the script
         empty <- clearDefs defs
         pure (!(quote empty env ntm), gnf env expected)
  where
    mkExpected : Maybe (Glued vars) -> Core (Term vars)
    mkExpected (Just ty) = pure !(getTerm ty)
    mkExpected Nothing
        = do nm <- genName "scriptTy"
             u <- uniVar fc
             metaVar fc erased env nm (TType fc u)
