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
data SVal : List Name -> Type where
     MkSVal : ForeignObj -> SchVars vars -> SVal vars

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
        SchemeMode -> Env Term vars -> Term vars -> Core (SVal vars)
seval mode env tm
    = do -- Check the evaluator is initialised. This will fail if the backend
         -- doesn't support scheme evaluation.
         True <- logTimeWhen False "Scheme eval" initialiseSchemeEval
              | False => throw (InternalError "Loading scheme support failed")

         -- make sure all the names in the term are compiled
         -- We need to recheck in advance, since definitions might have changed
         -- since we last evaluated a name, and we might have evaluated the
         -- name in a different mode
         let ms = getRefs (MN "" 0) tm
         let rs = addMetas ms tm
         names <- getAllNames empty (keys rs)
         traverse_ (compileDef mode) (keys names)
         
         i <- newRef Sym 0
         (bind, schEnv) <- mkEnv env id
         stm <- compile schEnv !(toFullNames tm)
         Just res <- coreLift $ evalSchemeObj (bind stm)
              | Nothing => throw (InternalError "Compiling expression failed")
         pure (MkSVal res schEnv)
  where
    mkEnv : forall vars . Ref Sym Integer =>
            Env Term vars ->
            (SchemeObj Write -> SchemeObj Write) ->
            Core (SchemeObj Write -> SchemeObj Write, SchVars vars)
    mkEnv [] k = pure (k, [])
--     mkEnv (Let v :: es) k
--         = do i <- nextName
--              (bind, vs) <- mkEnv es k
--              v' <- toScheme vs v
--              let n = "let-var-" ++ show i
--              pure (\x => "(let [(" ++ n ++ " " ++ v' ++ ")] " ++
--                                bind x ++ ")",
--                                Bound n :: vs)
    mkEnv (_ :: es) k
        = do i <- nextName
             (bind, vs) <- mkEnv es k
             pure (bind, Free ("free-" ++ show i) :: vs)

invalid : Core (Term vs)
invalid = pure (Erased emptyFC False)

getArgList : ForeignObj -> List ForeignObj
getArgList obj
    = if isPair obj
         then unsafeFst obj :: getArgList (unsafeSnd obj)
         else []

mutual
  -- We don't use decodeObj because then we have to traverse the term twice.
  -- Instead, decode the ForeignObj directly, which is uglier but faster.
  quoteVector : Ref Sym Integer =>
                SchVars (outer ++ vars) ->
                Integer -> List ForeignObj ->
                Core (Term (outer ++ vars))
  quoteVector svs (-2) [_, fname_in, args_in] -- Blocked app
      = do let Just fname = fromScheme (decodeObj fname_in)
                    | _ => invalid
           let argList = getArgList args_in
           args <- traverse (quote' svs) argList
           pure (apply emptyFC (Ref emptyFC Func fname) args)
  quoteVector svs (-10) [_, fn_arity, args_in] -- Blocked meta app
      = do let Just (fname, arity_in) = the (Maybe (Name, Integer)) $
                                            fromScheme (decodeObj fn_arity)
                    | _ => invalid
           let arity : Nat = cast arity_in
           let argList = getArgList args_in
           args <- traverse (quote' svs) argList
           pure (apply emptyFC (Meta emptyFC fname 0 (take arity args))
                               (drop arity args))
  quoteVector svs (-11) [_, loc_in, args_in] -- Blocked local var application
      = do loc <- quote' svs loc_in
           let argList = getArgList args_in
           args <- traverse (quote' svs) argList
           pure (apply emptyFC loc args)
  quoteVector svs (-1) (_ :: tag_in :: strtag :: cname_in :: fc_in :: args_in) -- TyCon
      = do let Just cname = fromScheme (decodeObj cname_in)
                    | Nothing => invalid
           let Just tag = the (Maybe Integer) $ fromScheme (decodeObj tag_in)
                    | Nothing => invalid
           let fc = emptyFC -- case fromScheme (decodeObj fc_in) of
--                            Just fc => fc
--                            _ => emptyFC
           args <- traverse (quote' svs) args_in
           pure (apply fc (Ref fc (TyCon (cast tag) (length args)) cname)
                           args)
  quoteVector svs (-15) [_, r_in, ty_in] -- Delayed
      = do ty <- quote' svs ty_in
           let r = case fromScheme (decodeObj r_in) of
                        Just r => r
                        _ => LUnknown
           pure (TDelayed emptyFC r ty)
  quoteVector svs (-4) [_, r_in, fc_in, ty_in, tm_in] -- Delay
      = do -- Block further reduction under tm_in
           Just _ <- coreLift $ evalSchemeStr "(ct-blockAll #t)"
                | Nothing => invalid
           let Procedure tmproc = decodeObj tm_in
                | _ => invalid
           let Procedure typroc = decodeObj ty_in
                | _ => invalid
           tm <- quote' svs (unsafeForce tmproc)
           ty <- quote' svs (unsafeForce typroc)
           -- Turn blocking off again
           Just _ <- coreLift $ evalSchemeStr "(ct-blockAll #f)"
                | Nothing => invalid
           let fc = case fromScheme (decodeObj fc_in) of
                         Just fc => fc
                         _ => emptyFC
           let r = case fromScheme (decodeObj r_in) of
                        Just r => r
                        _ => LUnknown
           pure (TDelay fc r ty tm)
  quoteVector svs (-5) [_, r_in, fc_in, tm_in] -- Force
      = do -- The thing we were trying to force was stuck. Corresponding to
           -- Core.Normalise, reduce it anyway here (so no ct-blockAll like above)
           tm <- quote' svs tm_in
           let fc = case fromScheme (decodeObj fc_in) of
                         Just fc => fc
                         _ => emptyFC
           let r = case fromScheme (decodeObj r_in) of
                        Just r => r
                        _ => LUnknown
           pure (TForce fc r tm)
  quoteVector svs (-6) [_, fc_in, imp_in] -- Erased
      = do let fc = case fromScheme (decodeObj fc_in) of
                         Just fc => fc
                         _ => emptyFC
           let imp = case fromScheme (decodeObj imp_in) of
                          Just imp => imp
                          _ => False
           pure (Erased fc imp)
  quoteVector svs (-7) [_, fc_in] -- Type
      = do let fc = case fromScheme (decodeObj fc_in) of
                         Just fc => fc
                         _ => emptyFC
           pure (TType fc)
  quoteVector svs (-8) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- Lambda
      = do let name = case fromScheme (decodeObj name_in) of
                           Nothing => UN "x"
                           Just n' => n'
           let rig = case fromScheme (decodeObj rig_in) of
                          Nothing => top
                          Just r => r
           ty <- quote' svs ty_in
           pi <- quotePiInfo svs pi_in
           quoteBinder svs Lam proc_in rig pi ty name
  quoteVector svs (-3) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- Pi
      = do let name = case fromScheme (decodeObj name_in) of
                           Nothing => UN "x"
                           Just n' => n'
           let rig = case fromScheme (decodeObj rig_in) of
                          Nothing => top
                          Just r => r
           ty <- quote' svs ty_in
           pi <- quotePiInfo svs pi_in
           quoteBinder svs Pi proc_in rig pi ty name
  quoteVector svs (-12) [_, proc_in, rig_in, pi_in, ty_in, name_in] -- PVar
      = do let name = case fromScheme (decodeObj name_in) of
                           Nothing => UN "x"
                           Just n' => n'
           let rig = case fromScheme (decodeObj rig_in) of
                          Nothing => top
                          Just r => r
           ty <- quote' svs ty_in
           pi <- quotePiInfo svs pi_in
           quoteBinder svs PVar proc_in rig pi ty name
  quoteVector svs (-13) [_, proc_in, rig_in, ty_in, name_in] -- PVTy
      = do let name = case fromScheme (decodeObj name_in) of
                           Nothing => UN "x"
                           Just n' => n'
           let rig = case fromScheme (decodeObj rig_in) of
                          Nothing => top
                          Just r => r
           ty <- quote' svs ty_in
           quoteBinder svs (\fc, r, p, t => PVTy fc r t) proc_in rig Explicit ty name
  quoteVector svs (-14) [_, proc_in, rig_in, val_in, ty_in, name_in] -- PLet
      = do let name = case fromScheme (decodeObj name_in) of
                           Nothing => UN "x"
                           Just n' => n'
           let rig = case fromScheme (decodeObj rig_in) of
                          Nothing => top
                          Just r => r
           ty <- quote' svs ty_in
           val <- quote' svs val_in
           quotePLet svs proc_in rig val ty name
  quoteVector svs (-9) [_, blocked, _] -- Blocked top level lambda
      = quote' svs blocked
  quoteVector svs (-100) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (I x')
  quoteVector svs (-101) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (I8 x')
  quoteVector svs (-102) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (I16 x')
  quoteVector svs (-103) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (I32 x')
  quoteVector svs (-104) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (I64 x')
  quoteVector svs (-105) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (BI x')
  quoteVector svs (-106) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (B8 x')
  quoteVector svs (-107) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (B16 x')
  quoteVector svs (-108) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (B32 x')
  quoteVector svs (-109) [_, x]
      = do let Just x' = fromScheme (decodeObj x)
                 | Nothing => invalid
           pure $ PrimVal emptyFC (B64 x')
  quoteVector svs tag (_ :: cname_in :: fc_in :: args_in) -- DataCon
      = if tag >= 0
           then do 
             let Just cname = fromScheme (decodeObj cname_in)
                    | Nothing => invalid
             let fc = emptyFC -- case fromScheme (decodeObj fc_in) of
--                            Just fc => fc
--                            _ => emptyFC
             args <- traverse (quote' svs) args_in
             pure (apply fc (Ref fc (DataCon (cast tag) (length args)) cname)
                            args)
           else invalid
  quoteVector _ _ _ = invalid

  quotePiInfo : Ref Sym Integer =>
                SchVars (outer ++ vars) ->
                ForeignObj ->
                Core (PiInfo (Term (outer ++ vars)))
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

  quoteBinder : Ref Sym Integer =>
                SchVars (outer ++ vars) ->
                (forall ty . FC -> RigCount -> PiInfo ty -> ty -> Binder ty) ->
                ForeignObj -> -- body of binder, represented as a function
                RigCount ->
                PiInfo (Term (outer ++ vars)) ->
                Term (outer ++ vars) -> -- decoded type
                Name -> -- bound name
                Core (Term (outer ++ vars))
  quoteBinder svs binder proc_in r pi ty name
      = do let Procedure proc = decodeObj proc_in
                    | _ => invalid
           i <- nextName
           let n = show name ++ "-" ++ show i
           let sc = unsafeApply proc (makeSymbol n)
           sc' <- quote' {outer = name :: outer} (Bound n :: svs) sc
           pure (Bind emptyFC name
                      (binder emptyFC r pi ty)
                      sc')

  quotePLet : Ref Sym Integer =>
              SchVars (outer ++ vars) ->
              ForeignObj -> -- body of binder, represented as a function
              RigCount ->
              Term (outer ++ vars) -> -- decoded type
              Term (outer ++ vars) -> -- decoded value
              Name -> -- bound name
              Core (Term (outer ++ vars))
  quotePLet svs proc_in r val ty name
      = do let Procedure proc = decodeObj proc_in
                    | _ => invalid
           i <- nextName
           let n = show name ++ "-" ++ show i
           let sc = unsafeApply proc (makeSymbol n)
           sc' <- quote' {outer = name :: outer} (Bound n :: svs) sc
           pure (Bind emptyFC name
                      (PLet emptyFC r val ty)
                      sc')

  quote' : Ref Sym Integer =>
           SchVars (outer ++ vars) -> ForeignObj ->
           Core (Term (outer ++ vars))
  quote' svs obj
      = if isVector obj
           then quoteVector svs (unsafeGetInteger (unsafeVectorRef obj 0))
                                (unsafeVectorToList obj)
        else if isProcedure obj then quoteBinder svs Lam obj top
                                              Explicit
                                              (Erased emptyFC False)
                                              (UN "x")
        else if isSymbol obj then pure $ findName svs (unsafeReadSymbol obj)
        else if isFloat obj then pure $ PrimVal emptyFC (Db (unsafeGetFloat obj))
        else if isInteger obj then pure $ PrimVal emptyFC (I (cast (unsafeGetInteger obj)))
        else if isString obj then pure $ PrimVal emptyFC (Str (unsafeGetString obj))
        else if isChar obj then pure $ PrimVal emptyFC (Ch (unsafeGetChar obj))
        else invalid
    where
      findName : forall vars . SchVars vars -> String -> Term vars
      findName [] n = Ref emptyFC Func (UN n)
      findName (x :: xs) n
          = if getName x == n
               then Local emptyFC Nothing _ First
               else let Local fc loc _ p = findName xs n
                           | _ => Ref emptyFC Func (UN n) in
                        Local fc loc _ (Later p)

      readVector : Integer -> Integer -> ForeignObj -> List ForeignObj
      readVector len i obj
          = if len == i
               then []
               else unsafeVectorRef obj i :: readVector len (i + 1) obj

export
quote : {auto c : Ref Ctxt Defs} ->
        SVal vars -> Core (Term vars)
quote (MkSVal val schEnv)
    = do i <- newRef Sym 0
         logTimeWhen False "Quote" $ quote' {outer = []} schEnv val
