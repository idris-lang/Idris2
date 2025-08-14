module TTImp.Elab.Quote

import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Reflect
import Core.Unify
import Core.TT

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Reflect
import TTImp.TTImp

%default covering

-- Collecting names and terms to let bind for unquoting
data Unq : Type where

-- Collect the escaped subterms in a term we're about to quote, and let bind
-- them first
mutual
  getUnquote : {auto c : Ref Ctxt Defs} ->
               {auto q : Ref Unq (List (Name, FC, RawImp))} ->
               {auto u : Ref UST UState} ->
               RawImp ->
               Core RawImp
  getUnquote (IPi fc c p n arg ret)
      = pure $ IPi fc c p n !(getUnquote arg) !(getUnquote ret)
  getUnquote (ILam fc c p n arg sc)
      = pure $ ILam fc c p n !(getUnquote arg) !(getUnquote sc)
  getUnquote (ILet fc lhsFC c n ty val sc)
      = pure $ ILet fc lhsFC c n !(getUnquote ty) !(getUnquote val) !(getUnquote sc)
  getUnquote (ICase fc opts sc ty cs)
      = pure $ ICase fc opts
                !(getUnquote sc) !(getUnquote ty)
                !(traverse getUnquoteClause cs)
  getUnquote (ILocal fc ds sc)
      = pure $ ILocal fc !(traverse getUnquoteDecl ds) !(getUnquote sc)
  getUnquote (IUpdate fc ds sc)
      = pure $ IUpdate fc !(traverse getUnquoteUpdate ds) !(getUnquote sc)
  getUnquote (IApp fc f a)
      = pure $ IApp fc !(getUnquote f) !(getUnquote a)
  getUnquote (IAutoApp fc f a)
      = pure $ IAutoApp fc !(getUnquote f) !(getUnquote a)
  getUnquote (INamedApp fc f n a)
      = pure $ INamedApp fc !(getUnquote f) n !(getUnquote a)
  getUnquote (IWithApp fc f a)
      = pure $ IWithApp fc !(getUnquote f) !(getUnquote a)
  getUnquote (IAlternative fc at as)
      = pure $ IAlternative fc at !(traverse getUnquote as)
  getUnquote (IRewrite fc f a)
      = pure $ IRewrite fc !(getUnquote f) !(getUnquote a)
  getUnquote (ICoerced fc t)
      = pure $ ICoerced fc !(getUnquote t)
  getUnquote (IBindHere fc m t)
      = pure $ IBindHere fc m !(getUnquote t)
  getUnquote (IAs fc nameFC u nm t)
      = pure $ IAs fc nameFC u nm !(getUnquote t)
  getUnquote (IMustUnify fc r t)
      = pure $ IMustUnify fc r !(getUnquote t)
  getUnquote (IDelayed fc r t)
      = pure $ IDelayed fc r !(getUnquote t)
  getUnquote (IDelay fc t)
      = pure $ IDelay fc !(getUnquote t)
  getUnquote (IForce fc t)
      = pure $ IForce fc !(getUnquote t)
  getUnquote (IQuote fc t)
      = pure $ IQuote fc !(getUnquote t)
  getUnquote (IUnquote fc tm)
      = do qv <- genVarName "q"
           update Unq ((qv, fc, tm) ::)
           pure (IUnquote fc (IVar fc qv)) -- turned into just qv when reflecting
  getUnquote tm = pure tm

  getUnquoteClause : {auto c : Ref Ctxt Defs} ->
                     {auto q : Ref Unq (List (Name, FC, RawImp))} ->
                     {auto u : Ref UST UState} ->
                     ImpClause ->
                     Core ImpClause
  getUnquoteClause (PatClause fc l r)
      = pure $ PatClause fc !(getUnquote l) !(getUnquote r)
  getUnquoteClause (WithClause fc l rig w prf flags cs)
      = pure $ WithClause
                 fc
                 !(getUnquote l)
                 rig
                 !(getUnquote w)
                 prf
                 flags
                 !(traverse getUnquoteClause cs)
  getUnquoteClause (ImpossibleClause fc l)
      = pure $ ImpossibleClause fc !(getUnquote l)

  getUnquoteUpdate : {auto c : Ref Ctxt Defs} ->
                     {auto q : Ref Unq (List (Name, FC, RawImp))} ->
                     {auto u : Ref UST UState} ->
                     IFieldUpdate ->
                     Core IFieldUpdate
  getUnquoteUpdate (ISetField p t) = pure $ ISetField p !(getUnquote t)
  getUnquoteUpdate (ISetFieldApp p t) = pure $ ISetFieldApp p !(getUnquote t)

  getUnquoteRecord : {auto c : Ref Ctxt Defs} ->
                     {auto q : Ref Unq (List (Name, FC, RawImp))} ->
                     {auto u : Ref UST UState} ->
                     ImpRecordData Name ->
                     Core (ImpRecordData Name)
  getUnquoteRecord (MkImpRecord header body)
        -- unlike before, we are also unquoting the default value, maybe this is important?
      = pure $ MkImpRecord !(traverse (traverse (traverse (traverse getUnquote))) header)
                           !(traverse (traverse (traverse (traverse getUnquote))) body)

  getUnquoteData : {auto c : Ref Ctxt Defs} ->
                   {auto q : Ref Unq (List (Name, FC, RawImp))} ->
                   {auto u : Ref UST UState} ->
                   ImpData ->
                   Core ImpData
  getUnquoteData (MkImpData fc n tc opts cs)
      = pure $ MkImpData fc n !(traverseOpt getUnquote tc) opts
                         !(traverse (traverse getUnquote) cs)
  getUnquoteData (MkImpLater fc n tc)
      = pure $ MkImpLater fc n !(getUnquote tc)

  getUnquoteDecl : {auto c : Ref Ctxt Defs} ->
                   {auto q : Ref Unq (List (Name, FC, RawImp))} ->
                   {auto u : Ref UST UState} ->
                   ImpDecl ->
                   Core ImpDecl
  getUnquoteDecl (IClaim (MkWithData fc (MkIClaimData c v opts ty)))
      = pure $ IClaim (MkWithData fc (MkIClaimData c v opts !(traverse getUnquote ty)))
  getUnquoteDecl (IData fc v mbt d)
      = pure $ IData fc v mbt !(getUnquoteData d)
  getUnquoteDecl (IDef fc v d)
      = pure $ IDef fc v !(traverse getUnquoteClause d)
  getUnquoteDecl (IParameters fc ps ds)
      = pure $ IParameters fc -- We also unquote default arguments here too
                           !(traverseList1 (traverse (traverse getUnquote)) ps)
                           !(traverse getUnquoteDecl ds)
  getUnquoteDecl (IRecord fc ns v mbt d)
      = pure $ IRecord fc ns v mbt !(traverse getUnquoteRecord d)
  getUnquoteDecl (INamespace fc ns ds)
      = pure $ INamespace fc ns !(traverse getUnquoteDecl ds)
  getUnquoteDecl (ITransform fc n l r)
      = pure $ ITransform fc n !(getUnquote l) !(getUnquote r)
  getUnquoteDecl d = pure d

bindUnqs : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           List (Name, FC, RawImp) ->
           RigCount -> ElabInfo -> NestedNames vars -> Env Term vars ->
           Term vars ->
           Core (Term vars)
bindUnqs [] _ _ _ _ tm = pure tm
bindUnqs ((qvar, fc, esctm) :: qs) rig elabinfo nest env tm
    = do defs <- get Ctxt
         Just (idx, gdef) <- lookupCtxtExactI (reflectionttimp "TTImp") (gamma defs)
              | _ => throw (UndefinedName fc (reflectionttimp "TTImp"))
         (escv, escty) <- check rig elabinfo nest env esctm
                                (Just (gnf env (Ref fc (TyCon 0)
                                           (Resolved idx))))
         sc <- bindUnqs qs rig elabinfo nest env tm
         pure (Bind fc qvar (Let fc (rigMult top rig) escv !(getTerm escty))
                    (refToLocal qvar qvar sc))

onLHS : ElabMode -> Bool
onLHS (InLHS _) = True
onLHS _ = False

export
checkQuote : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             {auto e : Ref EST (EState vars)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             RigCount -> ElabInfo ->
             NestedNames vars -> Env Term vars ->
             FC -> RawImp -> Maybe (Glued vars) ->
             Core (Term vars, Glued vars)
checkQuote rig elabinfo nest env fc tm exp
    = do defs <- get Ctxt
         q <- newRef Unq []
         tm' <- getUnquote tm
         qtm <- reflect fc defs (onLHS (elabMode elabinfo)) env tm'
         unqs <- get Unq
         qty <- getCon fc defs (reflectionttimp "TTImp")
         qtm <- bindUnqs unqs rig elabinfo nest env qtm
         fullqtm <- normalise defs env qtm
         checkExp rig elabinfo env fc fullqtm (gnf env qty) exp

export
checkQuoteName : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> Name -> Maybe (Glued vars) ->
                 Core (Term vars, Glued vars)
checkQuoteName rig elabinfo nest env fc n exp
    = do defs <- get Ctxt
         qnm <- reflect fc defs (onLHS (elabMode elabinfo)) env n
         qty <- getCon fc defs (reflectiontt "Name")
         checkExp rig elabinfo env fc qnm (gnf env qty) exp

export
checkQuoteDecl : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> List ImpDecl -> Maybe (Glued vars) ->
                 Core (Term vars, Glued vars)
checkQuoteDecl rig elabinfo nest env fc ds exp
    = do defs <- get Ctxt
         q <- newRef Unq []
         ds' <- traverse getUnquoteDecl ds
         qds <- reflect fc defs (onLHS (elabMode elabinfo)) env ds'
         unqs <- get Unq
         qd <- getCon fc defs (reflectionttimp "Decl")
         qty <- appCon fc defs (basics "List") [qd]
         checkExp rig elabinfo env fc
                  !(bindUnqs unqs rig elabinfo nest env qds)
                  (gnf env qty) exp
