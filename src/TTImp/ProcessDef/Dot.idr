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

dotIfInferred : FC -> RawImp -> Term vars -> Term vars
dotIfInferred fc rawArg arg = if isImplicit rawArg then dot fc arg else arg

addDots : {vars : _} ->
          (acc : SnocList (FC, Term vars)) ->
          (args : List (FC, Term vars)) ->
          (ty : Term vars') ->
          (expargs : List RawImp) ->
          (autoargs : List RawImp) ->
          (namedargs : List (Name, RawImp)) ->
          Core (List (FC, Term vars))
addDots acc ((fc, arg) :: args) (Bind _ n (Pi _ _ Explicit _) sc) (rawArg :: exps) autos named
    = addDots (acc :< (fc, dotIfInferred fc rawArg arg)) args sc exps autos named
addDots acc ((fc, arg) :: args) (Bind _ n (Pi _ _ AutoImplicit _) sc) exps (rawArg :: autos) named
    = addDots (acc :< (fc, dotIfInferred fc rawArg arg)) args sc exps autos named
addDots acc ((fc, arg) :: args) (Bind _ n (Pi _ _ Explicit _) sc) [] autos named
    = do case findNamed n named of
            Nothing =>
                throw $ InternalError "Impossible happened: explicit argument not found."
            Just ((_, rawArg), named) =>
                addDots (acc :< (fc, dotIfInferred fc rawArg arg)) args sc [] autos named
addDots acc ((fc, arg) :: args) (Bind _ n (Pi _ _ AutoImplicit _) sc) exps [] named
    = case findNamed n named of
            Nothing => do
                addDots (acc :< (fc, dot fc arg)) args sc exps [] named
            Just ((_, rawArg), named) =>
                addDots (acc :< (fc, dotIfInferred fc rawArg arg)) args sc exps [] named
addDots acc ((fc, arg) :: args) (Bind _ n (Pi _ _ Implicit _) sc) exps autos named
    = case findNamed n named of
           Nothing =>
               addDots (acc :< (fc, dot fc arg)) args sc exps [] named
           Just ((_, rawArg), named) =>
               addDots (acc :< (fc, dotIfInferred fc rawArg arg)) args sc exps autos named
addDots acc ((fc, arg) :: args) (Bind _ n (Pi _ _ (DefImplicit defArg) _) sc) exps autos named
    = case findNamed n named of
           Nothing =>
               addDots (acc :< (fc, dot fc arg)) args sc exps [] named
           Just ((_, rawArg), named) =>
               addDots (acc :< (fc, dotIfInferred fc rawArg arg)) args sc exps autos named
addDots acc [] ty [] [] [] = pure $ toList acc
addDots _ _ _ _ _ _
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

export
dotInferred : Ref Ctxt Defs =>
              {vars : _} ->
              NestedNames vars ->
              RawImp ->
              Term vars ->
              Core (Term vars)
dotInferred nest raw tm = go raw [] [] []
  where
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
             -- TODO: remove `the` after fix idris-lang/Idris2#3418
             let skip = maybe 0 (the (_ -> _) $ \(_, n, _) => length n) $
                                lookup nm (names nest) <|> lookup rawName (names nest)
                             -- ^ Local block put raw name in `NestedNames`
                             --   while parameters put `Resolved`.
                             --   So, we need to check both
             tynf <- normalise defs Env.empty (type def)
             (skipped, rest, Evidence _ ty') <- skipArgs skip [<] args tynf
             args' <- addDots skipped rest ty' exps autos named
             pure $ applyStackWithFC fn args'
    go _ _ _ _ = pure tm
