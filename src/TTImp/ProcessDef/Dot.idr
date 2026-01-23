module TTImp.ProcessDef.Dot

import Core.Context
import Core.Env
import Core.Normalise

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

export
dotInferred : Ref Ctxt Defs =>
              {vars : _} ->
              (topLevel : Bool) ->
              NestedNames vars ->
              RawImp ->
              Term vars ->
              Core (Term vars)

dotIfInferred : Ref Ctxt Defs =>
                {vars : _} ->
                NestedNames vars ->
                FC -> RawImp -> Term vars ->
                Core (Term vars)
dotIfInferred nest fc rawArg arg
    = if isImplicit rawArg
         then pure $ dot fc arg
         else dotInferred False nest rawArg arg

addDots : Ref Ctxt Defs =>
          {vars : _} ->
          NestedNames vars ->
          (acc : SnocList (FC, Term vars)) ->
          (args : List (FC, Term vars)) ->
          (ty : Term vars') ->
          (expargs : List RawImp) ->
          (autoargs : List RawImp) ->
          (namedargs : List (Name, RawImp)) ->
          Core (List (FC, Term vars))
addDots nest acc ((fc, arg) :: args) (Bind _ n (Pi _ _ Explicit _) sc) (rawArg :: exps) autos named
    = addDots nest (acc :< (fc, !(dotIfInferred nest fc rawArg arg))) args sc exps autos named
addDots nest acc ((fc, arg) :: args) (Bind _ n (Pi _ _ AutoImplicit _) sc) exps (rawArg :: autos) named
    = addDots nest (acc :< (fc, !(dotIfInferred nest fc rawArg arg))) args sc exps autos named
addDots nest acc ((fc, arg) :: args) (Bind _ n (Pi _ _ Explicit _) sc) [] autos named
    = do case findNamed n named of
            Nothing => case findBindAllExpPattern named of
                Nothing => throw $ InternalError "Impossible happened: explicit argument not found."
                Just rawArg =>
                    addDots nest (acc :< (fc, !(dotIfInferred nest fc rawArg arg))) args sc [] autos named
            Just ((_, rawArg), named) =>
                addDots nest (acc :< (fc, !(dotIfInferred nest fc rawArg arg))) args sc [] autos named
addDots nest acc ((fc, arg) :: args) (Bind _ n (Pi _ _ AutoImplicit _) sc) exps [] named
    = case findNamed n named of
            Nothing => do
                addDots nest (acc :< (fc, dot fc arg)) args sc exps [] named
            Just ((_, rawArg), named) =>
                addDots nest (acc :< (fc, !(dotIfInferred nest fc rawArg arg))) args sc exps [] named
addDots nest acc ((fc, arg) :: args) (Bind _ n (Pi _ _ Implicit _) sc) exps autos named
    = case findNamed n named of
           Nothing =>
               addDots nest (acc :< (fc, dot fc arg)) args sc exps [] named
           Just ((_, rawArg), named) =>
               addDots nest (acc :< (fc, !(dotIfInferred nest fc rawArg arg))) args sc exps autos named
addDots nest acc ((fc, arg) :: args) (Bind _ n (Pi _ _ (DefImplicit defArg) _) sc) exps autos named
    = case findNamed n named of
           Nothing =>
               addDots nest (acc :< (fc, dot fc arg)) args sc exps [] named
           Just ((_, rawArg), named) =>
               addDots nest (acc :< (fc, !(dotIfInferred nest fc rawArg arg))) args sc exps autos named
addDots nest acc [] ty [] [] named
    = if null $ filter (not . isBindAllExpPattern . fst) named
         then pure $ toList acc
         else throw $ InternalError "Impossible happened: arguments mismatch."
addDots _ _ _ _ _ _ _
    = throw $ InternalError $ "Impossible happened: arguments mismatch."

skipArgs : Nat ->
           (acc : SnocList (FC, Term vars)) ->
           (args : List (FC, Term vars)) ->
           (ty : Term vars') ->
           Core (SnocList (FC, Term vars), List (FC, Term vars), Exists Term)
skipArgs Z acc args ty = pure (acc, args, Evidence _ ty)
skipArgs (S n) acc (arg :: args) (Bind _ _ (Pi {}) sc)
    = skipArgs n (acc :< arg) args sc
skipArgs _ _ _ _
    = throw $ InternalError "Impossible happened: expected nested argument."

dotInferred topLevel nest raw tm = go raw [] [] []
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
             defs <- get Ctxt
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
             tynf <- normalise defs Env.empty (type def)
             (skipped, rest, Evidence _ ty') <- skipArgs skip [<] args tynf
             args' <- addDots nest skipped rest ty' exps autos named
             pure $ applyStackWithFC fn args'
    go _ _ _ _ = pure tm
