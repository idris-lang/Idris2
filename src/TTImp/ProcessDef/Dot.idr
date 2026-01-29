module TTImp.ProcessDef.Dot

import Core.Context
import Core.Env
import Core.Normalise
import Core.Value

import TTImp.TTImp
import TTImp.Elab.App

import Data.DPair
import Data.SnocList

isPattern : Term vars -> Bool
isPattern (App {}) = True
isPattern (Ref {}) = True
isPattern (TDelay {}) = True
isPattern (PrimVal {}) = True
isPattern (TType {}) = True
isPattern (Bind _ _ (Pi {}) _) = True
isPattern _ = False

isImplicit : RawImp -> Bool
isImplicit (Implicit {}) = True
isImplicit (IAs _ _ _ _ tm) = isImplicit tm
isImplicit _ = False

dot : FC -> Term vars -> Term vars
dot fc (As fc' s n tm) = As fc' s n $ dot fc tm
dot _ tm@(Erased {}) = tm
dot fc tm = if isPattern tm
               then Erased fc $ Dotted tm
               else tm

parameters {auto c : Ref Ctxt Defs} {vars : Scope}
           (defs : Defs) (nest : NestedNames vars) (env : Env Term vars)
  export
  dotInferred : (topLevel : Bool) ->
                RawImp ->
                Term vars ->
                Core (Term vars)

  dotIfInferred : FC -> RawImp -> Term vars ->
                  Core (Term vars)
  dotIfInferred fc rawArg arg
      = if isImplicit rawArg
           then pure $ dot fc arg
           else dotInferred False rawArg arg

  addDots : (acc : SnocList (FC, Term vars)) ->
            (ty : NF vars) ->
            (args : List (FC, Term vars)) ->
            (expargs : List RawImp) ->
            (autoargs : List RawImp) ->
            (namedargs : List (Name, RawImp)) ->
            Core (List (FC, Term vars))
  addDots acc (NBind _ n (Pi _ _ Explicit _) sc) ((fc, arg) :: args)  (rawArg :: exps) autos named
      = addDots (acc :< (fc, !(dotIfInferred fc rawArg arg)))
                !(sc defs $ toClosure defaultOpts env arg)
                args exps autos named
  addDots acc (NBind _ n (Pi _ _ AutoImplicit _) sc) ((fc, arg) :: args) exps (rawArg :: autos) named
      = addDots (acc :< (fc, !(dotIfInferred fc rawArg arg)))
                !(sc defs $ toClosure defaultOpts env arg)
                args exps autos named
  addDots acc (NBind _ n (Pi _ _ Explicit _) sc) ((fc, arg) :: args) [] autos named
      = do (arg', named') <- case findNamed n named of
               Nothing => case findBindAllExpPattern named of
                   Nothing => throw $ InternalError "Impossible happened: explicit argument not found."
                   Just rawArg => pure (!(dotIfInferred fc rawArg arg), named)
               Just ((_, rawArg), named') => pure (!(dotIfInferred fc rawArg arg), named')
           addDots (acc :< (fc, arg'))
                   !(sc defs $ toClosure defaultOpts env arg')
                   args [] autos named'
  addDots acc (NBind _ n (Pi _ _ AutoImplicit _) sc) ((fc, arg) :: args) exps [] named
      = do (arg', named') <- case findNamed n named of
               Nothing => pure (dot fc arg, named)
               Just ((_, rawArg), named') => pure (!(dotIfInferred fc rawArg arg), named')
           addDots (acc :< (fc, arg'))
                   !(sc defs $ toClosure defaultOpts env arg')
                   args exps [] named'
  addDots acc (NBind _ n (Pi _ _ Implicit _) sc) ((fc, arg) :: args) exps autos named
      = do (arg', named') <- case findNamed n named of
               Nothing => pure (dot fc arg, named)
               Just ((_, rawArg), named') => pure (!(dotIfInferred fc rawArg arg), named')
           addDots (acc :< (fc, arg'))
                   !(sc defs $ toClosure defaultOpts env arg')
                   args exps autos named'
  addDots acc (NBind _ n (Pi _ _ (DefImplicit defArg) _) sc) ((fc, arg) :: args) exps autos named
      = do (arg', named') <- case findNamed n named of
               Nothing => pure (dot fc arg, named)
               Just ((_, rawArg), named') => pure (!(dotIfInferred fc rawArg arg), named')
           addDots (acc :< (fc, arg'))
                   !(sc defs $ toClosure defaultOpts env arg')
                   args exps autos named'
  addDots acc ty [] [] [] named
      = if null $ filter (not . isBindAllExpPattern . fst) named
           then pure $ toList acc
           else throw $ InternalError "Impossible happened: arguments mismatch."
  addDots _ _ _ _ _ _
      = throw $ InternalError $ "Impossible happened: arguments mismatch."

  skipArgs : Nat ->
             (acc : SnocList (FC, Term vars)) ->
             (args : List (FC, Term vars)) ->
             (ty : NF vars) ->
             Core (SnocList (FC, Term vars), List (FC, Term vars), NF vars)
  skipArgs Z acc args ty = pure (acc, args, ty)
  skipArgs (S n) acc ((fc, arg) :: args) (NBind _ _ (Pi {}) sc)
      = skipArgs n (acc :< (fc, arg)) args !(sc defs $ toClosure defaultOpts env arg)
  skipArgs _ _  __
      = throw $ InternalError "Impossible happened: expected nested argument."

  dotInferred topLevel raw tm = go raw [] [] []
    where
      -- Don't dot primitives functions in argument position
      needsDot : Name -> Core Bool
      needsDot nm = if topLevel
                       then pure $ True
                       else pure $ not $ isPrimName !getPrimitiveNames nm

      go : RawImp ->
           (expargs : List RawImp) ->
           (autoargs : List RawImp) ->
           (namedargs : List (Name, RawImp)) ->
           Core (Term vars)
      go (IApp fc fn arg) exps autos named
         = go fn (arg :: exps) autos named
      go (IWithApp fc fn arg) exps autos named
         = go fn (arg :: exps) autos named
      go (IAutoApp fc fn arg) exps autos named
         = go fn exps (arg :: autos) named
      go (INamedApp fc fn nm arg) exps autos named
         = go fn exps autos ((nm, arg) :: named)
      go (IVar _ rawName) exps autos named
          = do let (fn@(Ref fc t nm), args) = getFnArgsWithFC tm
                 | _ => pure tm
               Just def <- lookupCtxtExact nm (gamma defs)
                 | Nothing => undefinedName fc nm
               True <- needsDot rawName
                 | _ => pure tm
               -- TODO: remove `the` after fix idris-lang/Idris2#3418
               let skip = maybe 0 (the (_ -> _) $ \(_, n, _) => length n) $
                                  lookup nm (names nest) <|> lookup rawName (names nest)
                               -- ^ Local block put raw name in `NestedNames`
                               --   while parameters put `Resolved`.
                               --   So, we need to check both
               tynf <- nf defs env $ embed $ type def
               (skipped, rest, ty') <- skipArgs skip [<] args tynf
               args' <- addDots skipped ty' rest exps autos named
               pure $ applyStackWithFC fn args'
      go (IPi _ _ _ _ aty _) [] [] []
         = case tm of
                Bind fc n (Pi bfc r p ty) sc
                   => pure $ Bind fc n (Pi bfc r p !(dotIfInferred bfc aty ty)) sc
                _ => throw $ InternalError "Expected Pi type, got \{show tm}"
      go (IPi _ _ _ _ aty _) exps autos named
         = throw $ InternalError "Unexpected arguments Pi-type with arguments: \{show raw}"
      go _ _ _ _ = pure tm
