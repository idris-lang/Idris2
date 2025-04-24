module Core.Evaluate.Convert

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Evaluate.Quote
import Core.Evaluate.Expand
import Core.TT

import Core.Evaluate.Normalise
import Core.Evaluate.Value

import Data.SnocList
import Data.Vect
import Libraries.Data.WithDefault

data QVar : Type where

data Strategy
  = Reduce (List Namespace) -- reduce applications, as long as we're
             -- in a namespace where the definition is visible
  | BlockApp -- block all applications. This is for when we've gone under a
             -- case so applications will be stuck

genName : Ref QVar Int => String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

genVar : Ref QVar Int => FC -> String -> Core (Value f vars)
genVar fc n
    = do var <- genName n
         pure (vRef fc Bound var)

-- TODO: Move to Core.TT.Universes
addConstraint : {auto c : Ref Ctxt Defs} -> UConstraint -> Core ()
addConstraint c
    = do defs <- get Ctxt
         put Ctxt ({ uconstraints $= (c ::) } defs)

parameters {auto c : Ref Ctxt Defs}
  convNF : {vars: _} -> Ref QVar Int =>
           Strategy -> Env Term vars ->
           NF vars -> NF vars -> Core Bool

  convGen : {vars: _} -> Ref QVar Int =>
            Strategy -> Env Term vars ->
            Value f vars -> Value f' vars -> Core Bool

  convSpine : {vars: _} -> Ref QVar Int =>
              Strategy -> Env Term vars ->
              Spine vars -> Spine vars -> Core Bool
  convSpine s env [<] [<] = pure True
  convSpine s env (xs :< x) (ys :< y)
      = do True <- convGen s env !(value x) !(value y) | False => pure False
           convSpine s env xs ys
  convSpine s env _ _ = pure False

  -- Applications which have been expanded, but not as far as 'case'
  convertAppsNF :
        {vars: _} ->
        Ref QVar Int =>
        Strategy -> Env Term vars ->
        NF vars -> NF vars ->
        Core Bool
  -- If they're both still applications, see if they convert.
  -- If they don't, see if they expand into Cases and continue if so
  convertAppsNF s env x@(VApp _ nt n args _) y@(VApp _ nt' n' args' _)
      = if n == n'
           then convSpine s env args args'
           else do x'@(VCase{}) <- expandCases x | _ => pure False
                   y'@(VCase{}) <- expandCases y | _ => pure False
                   -- See if the case blocks convert
                   convGen s env x' y'
  convertAppsNF s env (VApp{}) (VMeta{}) = pure False
  convertAppsNF s env (VMeta{}) (VApp{}) = pure False
  -- Expanded into something else, so we've made progress, so back to the top
  -- level converstion
  convertAppsNF s env x y = convGen s env x y

  convertApps :
        {vars: _} ->
        Ref QVar Int =>
        Strategy -> Env Term vars ->
        FC -> NameType -> Name -> Spine vars -> Value f vars ->
        FC -> NameType -> Name -> Spine vars -> Value f' vars ->
        Core Bool
  convertApps BlockApp env _ _ n args _ _ _ n' args' _
      = if n == n'
           then convSpine BlockApp env args args'
           else pure False
  convertApps s env fc nt n args x fn' nt' n' args' y
      = -- If n == n' we can try to save work by just checking arguments
        if n == n'
           -- Otherwise, convert the values (val and val')
           then do False <- convSpine BlockApp env args args'
                            -- Check without reducing first since it might save a lot of work
                            -- on success
                       | True => pure True
                   convertAppsNF s env !(expand x) !(expand y)
           else convertAppsNF s env !(expand x) !(expand y)

  -- Declared above
  -- convNF : {vars : _} ->
  --          Ref QVar Int =>
  --          Strategy -> Env Term vars ->
  --          NF vars -> NF vars -> Core Bool
  convNF s env (VBind _ _ (Lam fc _ _ ty) sc) (VBind _ _ (Lam _ _ _ ty') sc')
      = do True <- convGen s env ty ty' | False => pure False
           var <- genVar fc "conv"
           convGen s env !(sc $ pure var) !(sc' $ pure var)
  convNF {vars} s env tmx@(VBind fc x (Lam bfc r p ty) sc) tmy
      = do let etay = VBind fc x (Lam bfc r p ty) (apply fc tmy r)
           convGen {f'=Normal} s env tmx etay
  convNF {vars} s env tmx tmy@(VBind fc x (Lam bfc r p ty) sc)
      = do let etax = VBind fc x (Lam bfc r p ty) (apply fc tmx r)
           convGen {f=Normal} s env etax tmy
  convNF {vars} s env (VBind fc x b sc) (VBind fc' x' b' sc')
      = do True <- convBinders b b' | False => pure False
           var <- genVar fc "conv"
           convGen s env !(sc (pure var)) !(sc' (pure var))
    where
      sameBinders : Binder (Value f vars) -> Binder (Value f' vars) -> Bool
      sameBinders (Pi {}) (Pi {}) = True
      sameBinders (Lam {}) (Lam {}) = True
      sameBinders _ _ = False

      convPiInfo : PiInfo (Value f vars) -> PiInfo (Value f' vars) -> Core Bool
      convPiInfo Implicit Implicit = pure True
      convPiInfo Explicit Explicit = pure True
      convPiInfo AutoImplicit AutoImplicit = pure True
      convPiInfo (DefImplicit x) (DefImplicit y) = convGen s env x y
      convPiInfo _ _ = pure False

      convBinders : Binder (Value f vars) -> Binder (Value f' vars) -> Core Bool
      convBinders bx by
          = if sameBinders bx by && multiplicity bx == multiplicity by
               then allM id [ convPiInfo (piInfo bx) (piInfo by)
                            , convGen s env (binderType bx) (binderType by)]
               else pure False

  convNF s env x@(VApp fc nt n args val) y@(VApp fc' nt' n' args' val')
      = convertAppsNF s env x y
  convNF s env (VLocal _ i _ sp) (VLocal _ i' _ sp')
      = if i == i'
           then convSpine s env sp sp'
           else pure False
  convNF {vars} s env x@(VMeta _ _ i sc args val) y@(VMeta _ _ i' sc' args' val')
      = do Just x <- val  | Nothing => convMeta
           Just y <- val' | Nothing => convMeta
           convGen s env !(expand x) !(expand y)
    where
      convScope : List (RigCount, Core (Glued vars)) ->
                  List (RigCount, Core (Glued vars)) -> Core Bool
      convScope [] [] = pure True
      convScope ((_, x) :: xs) ((_, y) :: ys)
          = do True <- convGen s env !x !y | False => pure False
               convScope xs ys
      convScope _ _ = pure False

      convMeta : Core Bool
      convMeta
          = if i == i'
               then do True <- convScope sc sc' | False => pure False
                       convSpine s env args args'
               else pure False
  -- If one is a Metavar and the other isn't, try to reduce the Metavar first
--   convNF s env (VMeta _ _ _ _ _ val) y
--       = do Just x <- val | Nothing => pure False
--            convGen s env !(expand x) !(expand y)
--   convNF s env x (VMeta _ _ _ _ _ val)
--       = do Just y <- val | Nothing => pure False
--            convGen s env !(expand x) !(expand y)
  convNF s env (VDCon _ n t a sp) (VDCon _ n' t' a' sp')
      = if t == t'
           then convSpine s env sp sp'
           else pure False
  convNF s env (VTCon _ n a sp) (VTCon _ n' a' sp')
      = if n == n'
           then convSpine s env sp sp'
           else pure False
  convNF s env (VAs _ _ _ x) (VAs _ _ _ y) = convGen s env x y
  convNF {vars} s env (VCase fc t r sc ty alts) (VCase _ t' r' sc' ty' alts')
      = do True <- convGen s env sc sc' | False => pure False
           True <- convGen s env ty ty' | False => pure False
           convAlts alts alts'
   where
     blockIfPat : CaseType -> Strategy
     blockIfPat PatMatch = BlockApp
     blockIfPat _ = s

     convScope : (args : SnocList (RigCount, Name)) ->
                 VCaseScope args vars ->
                 (args' : SnocList (RigCount, Name)) ->
                 VCaseScope args' vars ->
                 Core Bool
     -- block applications to avoid reducing indefinitely
     convScope [<] sc [<] sc' = convGen (blockIfPat t) env (snd !sc) (snd !sc')
     convScope (xs :< x) sc (ys :< y) sc'
         = do xn <- genVar fc "arg"
              convScope xs (sc (pure xn)) ys (sc' (pure xn))
     convScope _ _ _ _ = pure False

     convAlt : VCaseAlt vars -> VCaseAlt vars -> Core Bool
     convAlt (VConCase _ n t args sc) (VConCase _ n' t' args' sc')
         = if t == t'
              then convScope args sc args' sc'
              else pure False
     convAlt (VDelayCase _ t a sc) (VDelayCase _ t' a' sc')
         = do tn <- genVar fc "t"
              an <- genVar fc "a"
              convGen BlockApp env (snd !(sc (pure tn) (pure an)))
                                   (snd !(sc' (pure tn) (pure an)))
     convAlt (VConstCase _ c x) (VConstCase _ c' y)
         = if c == c'
              then convGen BlockApp env x y
              else pure False
     convAlt (VDefaultCase _ x) (VDefaultCase _ y) = convGen BlockApp env x y
     convAlt _ _ = pure False

     convAlts : List (VCaseAlt vars) -> List (VCaseAlt vars) -> Core Bool
     convAlts [] [] = pure True
     convAlts (x :: xs) (y :: ys)
         = do True <- convAlt x y | False => pure False
              convAlts xs ys
     convAlts _ _ = pure False
  convNF s env (VDelayed _ r x) (VDelayed _ r' y)
      = if compatible r r'
           then convGen s env x y
           else pure False
  convNF s env (VDelay _ r _ x) (VDelay _ r' _ y)
      = if compatible r r'
           then convGen s env x y
           else pure False
  convNF s env (VForce _ r x spx) (VForce _ r' y spy)
      = if compatible r r'
           then do True <- convGen s env x y
                       | False => pure False
                   convSpine s env spx spy
           else pure False

  convNF s env (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
  convNF {vars} s env (VPrimOp _ fn args) (VPrimOp _ fn' args')
      = if sameFn fn fn'
           then convArgs args args'
           else pure False
    where
      convArgs : Vect n (Value f vars) -> Vect m (Value f' vars) -> Core Bool
      convArgs [] [] = pure True
      convArgs (x :: xs) (y :: ys)
          = do True <- convGen s env x y
                    | False => pure False
               convArgs xs ys
      convArgs _ _ = pure False
  convNF s env (VErased _ (Dotted t)) u = convGen s env t u
  convNF s env t (VErased _ (Dotted u)) = convGen s env t u
  convNF s env (VErased _ _) _ = pure True
  convNF s env _ (VErased _ _) = pure True
  convNF s env (VType fc n) (VType fc' n')
      = do addConstraint (ULE n n') --(ULE fc n fc' n')
           pure True
  convNF s env x y = pure False

  convGen s env x@(VApp fc nt n args val) y@(VApp fc' nt' n' args' val')
      = convertApps s env fc nt n args x fc' nt' n' args' y
  convGen s env x y = convNF s env !(expand x) !(expand y)

  namespace Value
    export
    convert : {vars: _} -> Env Term vars -> Value f vars -> Value f' vars -> Core Bool
    convert env x y
        = do q <- newRef QVar 0
             defs <- get Ctxt
             convGen (Reduce (currentNS defs :: nestedNS defs)) env x y

    export
    chkConvert : {vars : _} ->
                 FC -> Env Term vars -> Value f vars -> Value f' vars -> Core ()
    chkConvert fc env x y
        = do True <- convert env x y
                 | False => throw (CantConvert fc (gamma !(get Ctxt)) env
                                               !(quote env x)
                                               !(quote env y))
             pure ()

  namespace Term
    export
    convert : {vars: _} -> Env Term vars -> Term vars -> Term vars -> Core Bool
    convert env x y
        = do x' <- nf env x
             y' <- nf env y
             convert env x' y'

    export
    chkConvert : {vars : _} ->
                 FC -> Env Term vars -> Term vars -> Term vars -> Core ()
    chkConvert fc env x y
        = do True <- convert env x y
                 | False => throw (CantConvert fc (gamma !(get Ctxt)) env x y)
             pure ()
