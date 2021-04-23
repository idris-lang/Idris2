module Core.GetType

import Core.CaseTree
import Core.TT
import Core.Context
import Core.Env
import Core.Normalise
import Core.Value

%default covering

-- Get the type of an already typechecked thing.
-- We need this (occasionally) because we don't store types in subterms (e.g. on
-- applications) and we don't keep the type of suterms up to date throughout
-- unification. Perhaps we should? There's a trade off here, and recalculating on
-- the rare occasions it's necessary doesn't seem to cost too much, but keep an
-- eye on it...

mutual
  chk : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        Env Term vars -> Term vars -> Core (Glued vars)
  chk env (Local fc r idx p)
      = pure $ gnf env (binderType (getBinder p env))
  chk env (Ref fc nt n)
      = do defs <- get Ctxt
           Just ty <- lookupTyExact n (gamma defs)
               | Nothing => undefinedName fc n
           pure $ gnf env (embed ty)
  chk env (Meta fc n i args)
      = do defs <- get Ctxt
           Just mty <- lookupTyExact (Resolved i) (gamma defs)
               | Nothing => undefinedName fc n
           chkMeta fc env !(nf defs env (embed mty)) args
  chk env (Bind fc nm b sc)
      = do bt <- chkBinder env b
           sct <- chk {vars = nm :: _} (b :: env) sc
           pure $ gnf env (discharge fc nm b !(getTerm bt) !(getTerm sct))
  chk env (App fc f a)
      = do fty <- chk env f
           case !(getNF fty) of
                NBind _ _ (Pi _ _ _ ty) scdone =>
                      do defs <- get Ctxt
                         aty <- chk env a
                         sc' <- scdone defs (toClosure defaultOpts env a)
                         pure $ glueBack defs env sc'
                _ => do fty' <- getTerm fty
                        throw (NotFunctionType fc env fty')
  chk env (As fc s n p) = chk env p
  chk env (TDelayed fc r tm) = pure (gType fc)
  chk env (TDelay fc r dty tm)
      = do gtm <- chk env tm
           tm' <- getNF gtm
           defs <- get Ctxt
           pure $ glueBack defs env (NDelayed fc r tm')
  chk env (TForce fc r tm)
      = do tm' <- chk env tm
           case !(getNF tm') of
                NDelayed fc _ fty =>
                    do defs <- get Ctxt
                       pure $ glueBack defs env fty
                _ => throw (GenericMsg fc "Not a delayed type")
  chk env (PrimVal fc x) = pure $ gnf env (chkConstant fc x)
  chk env (TType fc) = pure (gType fc)
  chk env (Erased fc _) = pure (gErased fc)

  chkMeta : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            FC -> Env Term vars -> NF vars -> List (Term vars) ->
            Core (Glued vars)
  chkMeta fc env ty []
      = do defs <- get Ctxt
           pure $ glueBack defs env ty
  chkMeta fc env (NBind _ _ (Pi _ _ _ ty) scdone) (a :: args)
      = do defs <- get Ctxt
           aty <- chk env a
           sc' <- scdone defs (toClosure defaultOpts env a)
           chkMeta fc env sc' args
  chkMeta fc env ty args
      = do defs <- get Ctxt
           throw (NotFunctionType fc env !(quote defs env ty))

  chkBinder : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Env Term vars -> Binder (Term vars) -> Core (Glued vars)
  chkBinder env b = chk env (binderType b)

  discharge : FC -> (nm : Name) -> Binder (Term vars) ->
              Term vars -> Term (nm :: vars) -> (Term vars)
  discharge fc n (Lam fc' c x ty) bindty scopety
      = Bind fc n (Pi fc' c x ty) scopety
  discharge fc n (Let fc' c val ty) bindty scopety
      = Bind fc n (Let fc' c val ty) scopety
  discharge fc n (Pi _ _ _ _) bindty scopety
      = bindty
  discharge fc n (PVar fc' c p ty) bindty scopety
      = Bind fc n (PVTy fc' c ty) scopety
  discharge fc n (PLet fc' c val ty) bindty scopety
      = Bind fc n (PLet fc' c val ty) scopety
  discharge fc n (PVTy _ _ _) bindty scopety
      = bindty

  chkConstant : FC -> Constant -> Term vars
  chkConstant fc (I x) = PrimVal fc IntType
  chkConstant fc (BI x) = PrimVal fc IntegerType
  chkConstant fc (B8 x) = PrimVal fc Bits8Type
  chkConstant fc (B16 x) = PrimVal fc Bits16Type
  chkConstant fc (B32 x) = PrimVal fc Bits32Type
  chkConstant fc (B64 x) = PrimVal fc Bits64Type
  chkConstant fc (Str x) = PrimVal fc StringType
  chkConstant fc (Ch x) = PrimVal fc CharType
  chkConstant fc (Db x) = PrimVal fc DoubleType
  chkConstant fc WorldVal = PrimVal fc WorldType
  chkConstant fc _ = TType fc

export
getType : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          Env Term vars -> (term : Term vars) -> Core (Glued vars)
getType env term = chk env term
