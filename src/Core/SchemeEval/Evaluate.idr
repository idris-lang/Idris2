module Core.SchemeEval.Evaluate

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.SchemeEval.Compile
import Core.SchemeEval.ToScheme
import Core.TT

import Libraries.Data.NameMap
import Libraries.Utils.Scheme

public export
data SObj : SnocList Name -> Type where
     MkSObj : ForeignObj -> SchVars vars -> SObj vars

-- Values, which we read off evaluated scheme objects.
-- Unfortunately we can't quite get away with using Core.Value.NF because
-- of the different representation of closures. Also, we're call by value
-- when going via scheme, so this structure is a little bit simpler (not
-- recording a LocalEnv for example).
mutual
  public export
  data SHead : SnocList Name -> Type where
       SLocal : (idx : Nat) -> (0 p : IsVar nm idx vars) -> SHead vars
       SRef : NameType -> Name -> SHead vars
       SMeta : Name -> Int -> List (Core (SNF vars)) -> SHead vars

  public export
  data SNF : SnocList Name -> Type where
       SBind    : FC -> (x : Name) -> Binder (SNF vars) ->
                  (SObj vars -> Core (SNF vars)) -> SNF vars
       SApp     : FC -> SHead vars -> List (Core (SNF vars)) -> SNF vars
       SDCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  List (Core (SNF vars)) -> SNF vars
       STCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  List (Core (SNF vars)) -> SNF vars
       SDelayed : FC -> LazyReason -> SNF vars -> SNF vars
       SDelay   : FC -> LazyReason -> Core (SNF vars) -> Core (SNF vars) ->
                  SNF vars
       SForce   : FC -> LazyReason -> SNF vars -> SNF vars
       SPrimVal : FC -> Constant -> SNF vars
       SErased  : FC -> WhyErased (SNF vars) -> SNF vars
       SType    : FC -> Name -> SNF vars

getAllNames : {auto c : Ref Ctxt Defs} ->
              NameMap () -> List Name -> Core (NameMap ())
getAllNames done [] = pure done
getAllNames done (x :: xs)
    = do let Nothing = lookup x done
             | _ => getAllNames done xs
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact x (gamma defs)
             | _ => getAllNames done xs
         getAllNames (insert x () done) (xs ++ keys (refersTo gdef))

-- Evaluate a term via scheme. This will throw if the backend doesn't
-- support scheme evaluation, so callers should have checked first and fall
-- back to the internal (slow!) evaluator if initialisation fails.
export
seval : {auto c : Ref Ctxt Defs} ->
        SchemeMode -> Env Term vars -> Term vars -> Core (SObj vars)
seval mode env tm
    = do -- Check the evaluator is initialised. This will fail if the backend
         -- doesn't support scheme evaluation.
         True <- logTimeWhen False 0 "Scheme eval" initialiseSchemeEval
              | False => throw (InternalError "Loading scheme support failed")

         -- make sure all the names in the term are compiled
         -- We need to recheck in advance, since definitions might have changed
         -- since we last evaluated a name, and we might have evaluated the
         -- name in a different mode
         let ms = getRefs (MN "" 0) tm
         let rs = addMetas False ms tm
         names <- getAllNames empty (keys rs)
         traverse_ (compileDef mode) (keys names)

         i <- newRef Sym 0
         (bind, schEnv) <- mkEnv env id
         stm <- compile schEnv !(toFullNames tm)
         Just res <- coreLift $ evalSchemeObj (bind stm)
              | Nothing => throw (InternalError "Compiling expression failed")
         pure (MkSObj res schEnv)
  where
    mkEnv : forall vars . Ref Sym Integer =>
            Env Term vars ->
            (SchemeObj Write -> SchemeObj Write) ->
            Core (SchemeObj Write -> SchemeObj Write, SchVars vars)
    mkEnv [<] k = pure (k, [])
    mkEnv (es :< Let fc c val ty) k
        = do i <- nextName
             (bind, vs) <- mkEnv es k
             val' <- compile vs val
             let n = "let-var-" ++ show i
             pure (\x => Let n val' (bind x), Bound n :: vs)
    mkEnv (es :< _) k
        = do i <- nextName
             (bind, vs) <- mkEnv es k
             pure (bind, Free ("free-" ++ show i) :: vs)

invalid : Core (Term vs)
invalid = pure (Erased emptyFC Placeholder)

invalidS : Core (SNF vs)
invalidS = pure (SErased emptyFC Placeholder)

getArgList : ForeignObj -> List ForeignObj
getArgList obj
    = if isPair obj
         then unsafeFst obj :: getArgList (unsafeSnd obj)
         else []

quoteFC : ForeignObj -> FC
quoteFC fc_in = fromMaybe emptyFC (fromScheme (decodeObj fc_in))

quoteLazyReason : ForeignObj -> LazyReason
quoteLazyReason r_in = fromMaybe LUnknown (fromScheme (decodeObj r_in))

quoteTypeLevel : ForeignObj -> Name
quoteTypeLevel u_in = fromMaybe (MN "top" 0) (fromScheme (decodeObj u_in))

quoteRigCount : ForeignObj -> RigCount
quoteRigCount rig_in = fromMaybe top (fromScheme (decodeObj rig_in))

quoteBinderName : ForeignObj -> Name
quoteBinderName nm_in
  = fromMaybe (UN (Basic "x")) (fromScheme (decodeObj nm_in))

quoteOrInvalid : Scheme x =>
              ForeignObj -> (x -> Core (Term vars)) -> Core (Term vars)
quoteOrInvalid obj_in k = do
  let Just obj = fromScheme (decodeObj obj_in)
    | Nothing => invalid
  k obj

quoteOrInvalidS : Scheme x =>
                 ForeignObj -> (x -> Core (SNF vars)) -> Core (SNF vars)
quoteOrInvalidS obj_in k = do
  let Just obj = fromScheme (decodeObj obj_in)
    | Nothing => invalidS
  k obj

mutual

  -- We don't use decodeObj because then we have to traverse the term twice.
  -- Instead, decode the ForeignObj directly, which is uglier but faster.
  quoteVector : Ref Sym Integer =>
                Ref Ctxt Defs =>
                SchVars (vars ++ outer) ->
                Integer -> List ForeignObj ->
                Core (Term (vars ++ outer))
  quoteVector svs (-2) [_, fname_in, args_in] -- Blocked app
      = quoteOrInvalid fname_in $ \ fname => do
           let argList = getArgList args_in
           args <- traverse (quote' svs) argList
           pure (apply emptyFC (Ref emptyFC Func fname) args)
  quoteVector svs (-10) [_, fn_arity, args_in] -- Blocked meta app
      = quoteOrInvalid {x = (Name, Integer)} fn_arity $ \ (fname, arity_in) => do
           let arity : Nat = cast arity_in
           let argList = getArgList args_in
           args <- traverse (quote' svs) argList
           defs <- get Ctxt
           fnameF <- toFullNames fname
           (idx, _) <- getPosition fname (gamma defs)
           pure (apply emptyFC (Meta emptyFC fnameF idx (take arity args))
                               (drop arity args))
  quoteVector svs (-11) [_, loc_in, args_in] -- Blocked local var application
      = do loc <- quote' svs loc_in
           let argList = getArgList args_in
           args <- traverse (quote' svs) argList
           pure (apply emptyFC loc args)
  quoteVector svs (-1) (_ :: tag_in :: strtag :: cname_in :: fc_in :: args_in) -- TyCon
      = quoteOrInvalid cname_in $ \ cname =>
        quoteOrInvalid {x = Integer} tag_in $ \ tag => do
           let fc = emptyFC -- quoteFC fc_in
           args <- traverse (quote' svs) args_in
           pure (apply fc (Ref fc (TyCon (cast tag) (length args)) cname)
                           args)
  quoteVector svs (-15) [_, r_in, ty_in] -- Delayed
      = do ty <- quote' svs ty_in
           let r = quoteLazyReason r_in
           pure (TDelayed emptyFC r ty)
  quoteVector svs (-4) [_, r_in, fc_in, ty_in, tm_in] -- Delay
      = do -- Block further reduction under tm_in
           Just _ <- coreLift $ evalSchemeStr "(ct-setBlockAll #t)"
                | Nothing => invalid
           let Procedure tmproc = decodeObj tm_in
                | _ => invalid
           let Procedure typroc = decodeObj ty_in
                | _ => invalid
           tm <- quote' svs (unsafeForce tmproc)
           ty <- quote' svs (unsafeForce typroc)
           -- Turn blocking off again
           Just _ <- coreLift $ evalSchemeStr "(ct-setBlockAll #f)"
                | Nothing => invalid
           let fc = quoteFC fc_in
           let r = quoteLazyReason r_in
           pure (TDelay fc r ty tm)
  quoteVector svs (-5) [_, r_in, fc_in, tm_in] -- Force
      = do -- The thing we were trying to force was stuck. Corresponding to
           -- Core.Normalise, reduce it anyway here (so no ct-blockAll like above)
           tm <- quote' svs tm_in
           let fc = quoteFC fc_in
           let r = quoteLazyReason r_in
           pure (TForce fc r tm)
  quoteVector svs (-6) [_, fc_in, imp_in] -- Erased
      = do let fc = quoteFC fc_in
           imp <- quoteWhyErased (quote' svs) imp_in
           pure (Erased fc imp)
  quoteVector svs (-7) [_, fc_in, u_in] -- Type
      = do let fc = quoteFC fc_in
           let u = quoteTypeLevel u_in
           pure (TType fc u)
  quoteVector svs (-8) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- Lambda
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- quote' svs ty_in
           pi <- quotePiInfo svs pi_in
           quoteBinder svs Lam proc_in rig pi ty name
  quoteVector svs (-3) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- Pi
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- quote' svs ty_in
           pi <- quotePiInfo svs pi_in
           quoteBinder svs Pi proc_in rig pi ty name
  quoteVector svs (-12) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- PVar
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- quote' svs ty_in
           pi <- quotePiInfo svs pi_in
           quoteBinder svs PVar proc_in rig pi ty name
  quoteVector svs (-13) [_, proc_in, rig_in, ty_in, name_in] -- PVTy
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- quote' svs ty_in
           quoteBinder svs (\fc, r, p, t => PVTy fc r t) proc_in rig Explicit ty name
  quoteVector svs (-14) [_, proc_in, rig_in, val_in, ty_in, name_in] -- PLet
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- quote' svs ty_in
           val <- quote' svs val_in
           quotePLet svs proc_in rig val ty name
  quoteVector svs (-9) [_, blocked, _] -- Blocked top level lambda
      = quote' svs blocked
  quoteVector svs (-100) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (I x')
  quoteVector svs (-101) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (I8 x')
  quoteVector svs (-102) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (I16 x')
  quoteVector svs (-103) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (I32 x')
  quoteVector svs (-104) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (I64 x')
  quoteVector svs (-105) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (BI x')
  quoteVector svs (-106) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (B8 x')
  quoteVector svs (-107) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (B16 x')
  quoteVector svs (-108) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (B32 x')
  quoteVector svs (-109) [_, x]
      = quoteOrInvalid x $ \ x' => pure $ PrimVal emptyFC (B64 x')
  quoteVector svs tag (_ :: cname_in :: fc_in :: args_in) -- DataCon
      = if tag >= 0
           then quoteOrInvalid cname_in $ \ cname =>  do
             let fc = emptyFC -- quoteFC fc_in
             args <- traverse (quote' svs) args_in
             pure (apply fc (Ref fc (DataCon (cast tag) (length args)) cname)
                            args)
           else invalid
  quoteVector _ _ _ = invalid

  quotePiInfo : Ref Sym Integer =>
                Ref Ctxt Defs =>
                SchVars (vars ++ outer) ->
                ForeignObj ->
                Core (PiInfo (Term (vars ++ outer)))
  quotePiInfo svs obj
      = if isInteger obj
           then case unsafeGetInteger obj of
                     0 => pure Implicit
                     1 => pure Explicit
                     2 => pure AutoImplicit
                     _ => pure Explicit
           else if isBox obj
                   then do t' <- quote' svs (unsafeUnbox obj)
                           pure (DefImplicit t')
           else pure Explicit

  quoteWhyErased : (ForeignObj -> Core a) ->
                   ForeignObj ->
                   Core (WhyErased a)
  quoteWhyErased qt obj
      = if isInteger obj
           then case unsafeGetInteger obj of
                     0 => pure Impossible
                     _ => pure Placeholder
           else if isBox obj
                   then do t' <- qt (unsafeUnbox obj)
                           pure (Dotted t')
           else pure Placeholder

  quoteBinder : Ref Sym Integer =>
                Ref Ctxt Defs =>
                SchVars (vars ++ outer) ->
                (forall ty . FC -> RigCount -> PiInfo ty -> ty -> Binder ty) ->
                ForeignObj -> -- body of binder, represented as a function
                RigCount ->
                PiInfo (Term (vars ++ outer)) ->
                Term (vars ++ outer) -> -- decoded type
                Name -> -- bound name
                Core (Term (vars ++ outer))
  quoteBinder svs binder proc_in r pi ty name
      = do let Procedure proc = decodeObj proc_in
                    | _ => invalid
           i <- nextName
           let n = show name ++ "-" ++ show i
           let sc = unsafeApply proc (makeSymbol n)
           sc' <- quote' {outer = outer :< name} (Bound n :: svs) sc
           pure (Bind emptyFC name
                      (binder emptyFC r pi ty)
                      sc')

  quotePLet : Ref Sym Integer =>
              Ref Ctxt Defs =>
              SchVars (vars ++ outer) ->
              ForeignObj -> -- body of binder, represented as a function
              RigCount ->
              Term (vars ++ outer) -> -- decoded type
              Term (vars ++ outer) -> -- decoded value
              Name -> -- bound name
              Core (Term (vars ++ outer))
  quotePLet svs proc_in r val ty name
      = do let Procedure proc = decodeObj proc_in
                    | _ => invalid
           i <- nextName
           let n = show name ++ "-" ++ show i
           let sc = unsafeApply proc (makeSymbol n)
           sc' <- quote' {outer = outer :< name} (Bound n :: svs) sc
           pure (Bind emptyFC name
                      (PLet emptyFC r val ty)
                      sc')

  quote' : Ref Sym Integer =>
           Ref Ctxt Defs =>
           SchVars (vars ++ outer) -> ForeignObj ->
           Core (Term (vars ++ outer))
  quote' svs obj
      = if isVector obj
           then quoteVector svs (unsafeGetInteger (unsafeVectorRef obj 0))
                                (unsafeVectorToList obj)
        else if isProcedure obj then quoteBinder svs Lam obj top
                                              Explicit
                                              (Erased emptyFC Placeholder)
                                              (UN (Basic "x"))
        else if isSymbol obj then pure $ findName svs (unsafeReadSymbol obj)
        else if isFloat obj then pure $ PrimVal emptyFC (Db (unsafeGetFloat obj))
        else if isInteger obj then pure $ PrimVal emptyFC (I (cast (unsafeGetInteger obj)))
        else if isString obj then pure $ PrimVal emptyFC (Str (unsafeGetString obj))
        else if isChar obj then pure $ PrimVal emptyFC (Ch (unsafeGetChar obj))
        else invalid
    where
      findName : forall vars . SchVars vars -> String -> Term vars
      findName [] n = Ref emptyFC Func (UN (Basic n))
      findName (x :: xs) n
          = if getName x == n
               then Local emptyFC Nothing _ First
               else let Local fc loc _ p = findName xs n
                           | _ => Ref emptyFC Func (UN (Basic n)) in
                        Local fc loc _ (Later p)

      readVector : Integer -> Integer -> ForeignObj -> List ForeignObj
      readVector len i obj
          = if len == i
               then []
               else unsafeVectorRef obj i :: readVector len (i + 1) obj

-- Quote a scheme value directly back to a Term, without making an SNF
-- in between. This is what we want if we're just looking for a normal
-- form immediately (so, evaluating under binders)
export
quoteObj : {auto c : Ref Ctxt Defs} ->
           SObj vars -> Core (Term vars)
quoteObj (MkSObj val schEnv)
    = do i <- newRef Sym 0
         quote' {outer = [<]} schEnv val

mutual
  snfVector : Ref Ctxt Defs =>
              SchVars vars ->
              Integer -> List ForeignObj ->
              Core (SNF vars)
  snfVector svs (-2) [_, fname_in, args_in] -- Blocked application
      = quoteOrInvalidS fname_in $ \ fname => do
           let args = map (snf' svs) (getArgList args_in)
           pure (SApp emptyFC (SRef Func fname) args)
  snfVector svs (-10) [_, fn_arity, args_in] -- Block meta app
      = quoteOrInvalidS {x = (Name, Integer)} fn_arity $ \ (fname, arity_in) => do
           let arity : Nat = cast arity_in
           let args = map (snf' svs) (getArgList args_in)
           defs <- get Ctxt
           fnameF <- toFullNames fname
           (idx, _) <- getPosition fnameF (gamma defs)
           pure (SApp emptyFC (SMeta fnameF idx (take arity args))
                               (drop arity args))
  snfVector svs (-11) [_, loc_in, args_in] -- Blocked local var application
      = do SApp fc loc args <- snf' svs loc_in
                | _ => invalidS
           let args' = map (snf' svs) (getArgList args_in)
           pure (SApp fc loc (args ++ args'))
  snfVector svs (-1) (_ :: tag_in :: strtag :: cname_in :: fc_in :: args_in) -- TyCon
      = quoteOrInvalidS cname_in $ \ cname =>
        quoteOrInvalidS {x = Integer} tag_in $ \ tag => do
           let fc = quoteFC fc_in
           let args = map (snf' svs) args_in
           pure (STCon fc cname (cast tag) (length args) args)
  snfVector svs (-15) [_, r_in, ty_in] -- Delayed
      = do ty <- snf' svs ty_in
           let r = quoteLazyReason r_in
           pure (SDelayed emptyFC r ty)
  snfVector svs (-4) [_, r_in, fc_in, ty_in, tm_in] -- Delay
      = do let Procedure tmproc = decodeObj tm_in
                | _ => invalidS
           let Procedure typroc = decodeObj ty_in
                | _ => invalidS
           -- Block further reduction under tm_in
           let tm = do Just _ <- coreLift $ evalSchemeStr "(ct-setBlockAll #t)"
                            | Nothing => invalidS
                       res <- snf' svs (unsafeForce tmproc)
                       Just _ <- coreLift $ evalSchemeStr "(ct-setBlockAll #f)"
                            | Nothing => invalidS
                       pure res
           let ty = snf' svs (unsafeForce typroc)
           let fc = quoteFC fc_in
           let r = quoteLazyReason r_in
           pure (SDelay fc r ty tm)
  snfVector svs (-5) [_, r_in, fc_in, tm_in] -- Force
      = do -- The thing we were trying to force was stuck. Corresponding to
           -- Core.Normalise, reduce it anyway here (so no ct-blockAll like above)
           tm <- snf' svs tm_in
           let fc = quoteFC fc_in
           let r = quoteLazyReason r_in
           pure (SForce fc r tm)
  snfVector svs (-6) [_, fc_in, imp_in] -- Erased
      = do let fc = quoteFC fc_in
           imp <- quoteWhyErased (snf' svs) imp_in
           pure (SErased fc imp)
  snfVector svs (-7) [_, fc_in, u_in] -- Type
      = do let fc = quoteFC fc_in
           let u = quoteTypeLevel u_in
           pure (SType fc u)
  snfVector svs (-8) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- Lambda
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- snf' svs ty_in
           pi <- snfPiInfo svs pi_in
           snfBinder svs Lam proc_in rig pi ty name
  snfVector svs (-3) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- Pi
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- snf' svs ty_in
           pi <- snfPiInfo svs pi_in
           snfBinder svs Pi proc_in rig pi ty name
  snfVector svs (-12) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- PVar
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- snf' svs ty_in
           pi <- snfPiInfo svs pi_in
           snfBinder svs PVar proc_in rig pi ty name
  snfVector svs (-13) [_, proc_in, rig_in, ty_in, name_in] -- PVTy
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- snf' svs ty_in
           snfBinder svs (\fc, r, p, t => PVTy fc r t) proc_in rig Explicit ty name
  snfVector svs (-14) [_, proc_in, rig_in, val_in, ty_in, name_in] -- PLet
      = do let name = quoteBinderName name_in
           let rig = quoteRigCount rig_in
           ty <- snf' svs ty_in
           val <- snf' svs val_in
           snfPLet svs proc_in rig val ty name
  snfVector svs (-9) [_, blocked, _] -- Blocked top level lambda
      = snf' svs blocked

  -- constants here
  snfVector svs (-100) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (I x')
  snfVector svs (-101) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (I8 x')
  snfVector svs (-102) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (I16 x')
  snfVector svs (-103) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (I32 x')
  snfVector svs (-104) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (I64 x')
  snfVector svs (-105) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (BI x')
  snfVector svs (-106) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (B8 x')
  snfVector svs (-107) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (B16 x')
  snfVector svs (-108) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (B32 x')
  snfVector svs (-109) [_, x]
      = quoteOrInvalidS x $ \ x' => pure $ SPrimVal emptyFC (B64 x')

  snfVector svs tag (_ :: cname_in :: fc_in :: args_in) -- DataCon
      = if tag >= 0
           then quoteOrInvalidS cname_in $ \ cname => do
             let fc = quoteFC fc_in
             let args = map (snf' svs) args_in
             pure (SDCon fc cname (cast tag) (length args) args)
           else invalidS
  snfVector _ _ _ = invalidS

  snfPiInfo : Ref Ctxt Defs =>
              SchVars vars ->
              ForeignObj ->
              Core (PiInfo (SNF vars))
  snfPiInfo svs obj
      = if isInteger obj
           then case unsafeGetInteger obj of
                     0 => pure Implicit
                     1 => pure Explicit
                     2 => pure AutoImplicit
                     _ => pure Explicit
           else if isBox obj
                   then do t' <- snf' svs (unsafeUnbox obj)
                           pure (DefImplicit t')
           else pure Explicit

  snfBinder : Ref Ctxt Defs =>
              SchVars vars ->
              (forall ty . FC -> RigCount -> PiInfo ty -> ty -> Binder ty) ->
              ForeignObj -> -- body of binder, represented as a function
              RigCount ->
              PiInfo (SNF vars) ->
              SNF vars -> -- decoded type
              Name -> -- bound name
              Core (SNF vars)
  snfBinder svs binder proc_in r pi ty name
      = do let Procedure proc = decodeObj proc_in
                    | _ => invalidS
           pure (SBind emptyFC name (binder emptyFC r pi ty)
                       (\tm => do let MkSObj arg _ = tm
                                  let sc = unsafeApply proc arg
                                  snf' svs sc))

  snfPLet : Ref Ctxt Defs =>
            SchVars vars ->
            ForeignObj -> -- body of binder, represented as a function
            RigCount ->
            SNF vars -> -- decoded type
            SNF vars -> -- decoded value
            Name -> -- bound name
            Core (SNF vars)
  snfPLet svs proc_in r val ty name
      = do let Procedure proc = decodeObj proc_in
                    | _ => invalidS
           pure (SBind emptyFC name (PLet emptyFC r val ty)
                       (\tm => do let MkSObj arg _ = tm
                                  let sc = unsafeApply proc arg
                                  snf' svs sc))

  snf' : Ref Ctxt Defs =>
         SchVars vars -> ForeignObj ->
         Core (SNF vars)
  snf' svs obj
      = if isVector obj
           then snfVector svs (unsafeGetInteger (unsafeVectorRef obj 0))
                              (unsafeVectorToList obj)
           else if isProcedure obj then snfBinder svs Lam obj top
                                                 Explicit
                                                 (SErased emptyFC Placeholder)
                                                 (UN (Basic "x"))
           else if isSymbol obj then pure $ findName svs (unsafeReadSymbol obj)
           else if isFloat obj then pure $ SPrimVal emptyFC (Db (unsafeGetFloat obj))
           else if isInteger obj then pure $ SPrimVal emptyFC (I (cast (unsafeGetInteger obj)))
           else if isString obj then pure $ SPrimVal emptyFC (Str (unsafeGetString obj))
           else if isChar obj then pure $ SPrimVal emptyFC (Ch (unsafeGetChar obj))
           else invalidS
    where
      findName : forall vars . SchVars vars -> String -> SNF vars
      findName [] n = SApp emptyFC (SRef Func (UN (Basic n))) []
      findName (x :: xs) n
          = if getName x == n
               then SApp emptyFC (SLocal _ First) []
               else let SApp fc (SLocal _ p) args = findName xs n
                           | _ => SApp emptyFC (SRef Func (UN (Basic n))) [] in
                        SApp fc (SLocal _ (Later p)) []

      readVector : Integer -> Integer -> ForeignObj -> List ForeignObj
      readVector len i obj
          = if len == i
               then []
               else unsafeVectorRef obj i :: readVector len (i + 1) obj

export
toSNF : Ref Ctxt Defs =>
        SObj vars -> Core (SNF vars)
toSNF (MkSObj val schEnv) = snf' schEnv val
