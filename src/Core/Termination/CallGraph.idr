module Core.Termination.CallGraph

import Core.Context.Log
import Core.Env
import Core.Options
import Core.Evaluate.Value
import Core.Evaluate.Normalise
import Core.Evaluate
import Core.Name.CompatibleVars

import Data.String
import Data.SnocList.Quantifiers

import Libraries.Data.NameMap
import Libraries.Data.NameMap.Traversable
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SparseMatrix
import Data.SortedMap
import Data.Vect

%default covering

-- Drop any non-inf top level laziness annotations
-- Remove all force and delay annotations which are nothing to do with
-- coinduction meaning that all Delays left guard coinductive calls.
dropLazy : {auto c : Ref Ctxt Defs} -> Value f vars -> Core (Glued vars)
dropLazy val@(VDelayed _ r t)
    = case r of
           LInf => pure (asGlued val)
           _ => pure t
dropLazy val@(VDelay _ r t v)
    = case r of
           LInf => pure (asGlued val)
           _ => pure v
dropLazy val@(VForce fc r v sp)
    = case r of
           LInf => pure (asGlued val)
           _ => applyAll fc v (cast (map (\ e => (multiplicity e, value e)) sp))
dropLazy val = pure (asGlued val)

Substitutions : Type
Substitutions = NameMap (SnocList (Glued [<]))

scEq : {auto c : Ref Ctxt Defs} -> Substitutions -> Value f [<] -> Value f' [<] -> Core Bool

scEqSpine : {auto c : Ref Ctxt Defs} -> Substitutions -> Spine [<] -> Spine [<] -> Core Bool
scEqSpine _ [<] [<] = pure True
scEqSpine substs (sp :< x) (sp' :< y)
    = do x' <- value x
         y' <- value y
         if !(scEq substs x' y')
            then scEqSpine substs sp sp'
            else pure False
scEqSpine _ _ _ = pure False

-- Approximate equality between values. We don't go under binders - we're
-- only checking for size change equality so expect to just see type and
-- data constructors
-- TODO: size change for pattern matching on types
scEq' : {auto c : Ref Ctxt Defs} -> Substitutions -> Value f [<] -> Value f' [<] -> Core Bool
scEq' substs (VApp _ _ n sp _) (VApp _ _ n' sp' _)
    = if n == n'
         then scEqSpine substs sp sp'
         else pure False
-- Should never see this since we always call with vars = [<], but it is
-- technically possible
scEq' substs (VLocal _ idx _ sp) (VLocal _ idx' _ sp')
    = if idx == idx'
         then scEqSpine substs sp sp'
         else pure False
scEq' substs (VDCon _ _ t a sp) (VDCon _ _ t' a' sp')
    = if t == t'
         then scEqSpine substs sp sp'
         else pure False
scEq' substs (VTCon _ n a sp) (VTCon _ n' a' sp')
    = if n == n'
         then scEqSpine substs sp sp'
         else pure False
scEq' substs (VMeta _ _ i _ args _) (VMeta _ _ i' _ args' _)
   -- = i == i' && assert_total (all (uncurry (scEq substs)) (zip args args'))
   = pure $ i == i' && assert_total !(allM (uncurry (scEq substs)) !paired_values)
   where
     paired_values : Core (SnocList (Value Glue [<], Value Glue [<]))
     paired_values = traverse (\(a, a') => pure (!a, !a')) (zip (map value args) (map value args'))
scEq' substs (VAs _ _ a p) p' = pure $ !(scEq substs p p') || !(scEq substs p a)
scEq' substs p (VAs _ _ a p') = pure $ !(scEq substs p a) || !(scEq substs p p')
scEq' substs (VDelayed _ _ t) (VDelayed _ _ t') = scEq substs t t'
scEq' substs (VDelay _ _ t x) (VDelay _ _ t' x')
     = if !(scEq substs t t') then scEq substs x x'
          else pure False
scEq' substs (VForce _ _ t [<]) (VForce _ _ t' [<]) = scEq substs t t'
scEq' substs (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
-- traverse dotted LHS terms
scEq' substs t (VErased _ (Dotted t')) = scEq substs t t' -- t' is no longer a pattern
--scEq' _ (VErased _ _) (VErased _ _) = pure True
scEq' _ (VErased _ _) (VErased _ _) = pure True
scEq' _ (VUnmatched _ _) (VUnmatched _ _) = pure True
scEq' _ (VType _ _) (VType _ _) = pure True
scEq' _ _ _ = pure False -- other cases not checkable

scEq substs x y = scEqAppBound substs !(dropLazy x) !(dropLazy y)
  where
    scEqAppBound : Substitutions -> Glued [<] -> Glued [<] -> Core Bool
    scEqAppBound substs s t@(VApp _ Bound nm _ _)
        = if !(scEq' substs s t) then pure True
             else
              let Just ts = lookup nm substs | _ => pure False
              in anyM (scEq substs s) $ toList ts
    scEqAppBound substs s t = scEq' substs s t

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

knownOr : Core SizeChange -> Core SizeChange -> Core SizeChange
knownOr x y = case !x of Unknown => y; _ => x

plusLazy : Core SizeChange -> Core SizeChange -> Core SizeChange
plusLazy x y = case !x of Smaller => pure Smaller; x => pure $ x |+| !y

-- Return whether first argument is structurally smaller than the second.
sizeCompare : {auto c : Ref Ctxt Defs} ->
              {auto defs : Defs} ->
              Substitutions ->
              Nat -> -- backtracking fuel
              Glued [<] -> -- RHS: term we're checking
              Glued [<] -> -- LHS: argument it might be smaller than
              Core SizeChange

sizeCompare' : {auto c : Ref Ctxt Defs} ->
                    {auto defs : Defs} ->
                    Substitutions -> Nat -> Glued [<] -> Glued [<] -> Core SizeChange

sizeCompare substs fuel s t@(VApp _ Bound nm _ _)
    = do direct <- sizeCompare' substs fuel s t
         case direct of
           Unknown => case lookup nm substs of
             Nothing => pure Unknown
             Just ts => plusLazyList substs fuel s (toList ts)
           change => pure change
      where
        plusLazyList : Substitutions -> Nat -> Glued [<] -> List (Glued [<]) -> Core SizeChange
        plusLazyList substs fuel s [] = pure Unknown
        plusLazyList substs fuel s (t :: ts)
            = plusLazy (sizeCompare substs fuel s t) (plusLazyList substs fuel s ts)
sizeCompare substs fuel s t = sizeCompare' substs fuel s t

sizeCompareCon : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Substitutions -> Nat -> Glued [<] -> Glued [<] -> Core Bool
sizeCompareTyCon : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Substitutions -> Nat -> Glued [<] -> Glued [<] -> Core Bool
sizeCompareConArgs : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Substitutions -> Nat -> Glued [<] -> List (Glued [<]) -> Core Bool
sizeCompareApp : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Substitutions -> Nat -> Glued [<] -> Glued [<] -> Core SizeChange

sizeCompare' substs fuel s (VErased _ (Dotted t)) = sizeCompare substs fuel s t
sizeCompare' substs fuel _ (VErased _ _) = pure Unknown -- incomparable!
-- for an as pattern, it's smaller if it's smaller than either part
sizeCompare' substs fuel s (VAs _ _ p t)
    = knownOr (sizeCompare substs fuel s p) (sizeCompare substs fuel s t)
sizeCompare' substs fuel (VAs _ _ p s) t
    = knownOr (sizeCompare substs fuel p t) (sizeCompare substs fuel s t)
-- if they're both metas, let scEq check if they're the same
sizeCompare' substs fuel s@(VMeta _ _ _ _ _ _) t@(VMeta _ _ _ _ _ _) = pure (if !(scEq substs s t) then Same else Unknown)
-- otherwise try to expand RHS meta
sizeCompare' substitutions fuel s@(VMeta _ n i args _ _) t = do
  Just gdef <- lookupCtxtExact (Resolved i) (gamma defs) | _ => pure Unknown
  let (Function _ tm _ _) = definition gdef | _ => pure Unknown
  tm <- substMeta (embed tm) !(traverse snd args) zero [<]
  sizeCompare substitutions fuel tm t
  where
    substMeta : {0 drop : _} ->
                Term (Scope.addInner Scope.empty drop) -> List (Glued Scope.empty) ->
                SizeOf drop -> Subst Glued drop Scope.empty ->
                Core (Glued Scope.empty)
    substMeta (Bind bfc n (Lam _ c e ty) sc) (a :: as) drop env
        = substMeta sc as (suc drop) (env :< a)
    substMeta (Bind bfc n (Let _ c val ty) sc) as drop env
        = substMeta (subst val sc) as drop env
    substMeta rhs [] drop env = (nf [<] (substs drop !(to_env env) rhs))
      where
        to_env : {0 drop : _} -> Subst Glued drop Scope.empty -> Core (SubstEnv drop Scope.empty)
        to_env [<] = pure [<]
        to_env (as :< a) = pure $ !(to_env as) :< !(quote [<] a)
    substMeta rhs _ _ _ = throw (InternalError ("Badly formed metavar solution \{show n}"))

sizeCompare' substs fuel s t
   = if !(sizeCompareTyCon substs fuel s t) then pure Same
     else if !(sizeCompareCon substs fuel s t)
        then pure Smaller
        else knownOr (sizeCompareApp substs fuel s t) (pure $ if !(scEq substs s t) then Same else Unknown)

sizeCompareProdConArgs : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Substitutions -> Nat -> List (Glued [<]) -> List (Glued [<]) -> Core SizeChange
sizeCompareProdConArgs _ _ [] [] = pure Same
sizeCompareProdConArgs substs fuel (x :: xs) (y :: ys) =
  case !(sizeCompare substs fuel x y) of
    Unknown => pure Unknown
    t => (t |*|) <$> sizeCompareProdConArgs substs fuel xs ys
sizeCompareProdConArgs _ _ _ _ = pure Unknown

sizeCompareTyCon substs fuel s t =
  case t of
    VTCon _ cn _ args => case s of
      VTCon _ cn' _ args' => if cn == cn'
          then (Unknown /=) <$> sizeCompareProdConArgs substs fuel (toList !(traverseSnocList value args')) (toList !(traverseSnocList value args))
          else pure False
      _ => pure False
    _ => pure False

sizeCompareCon substs fuel s t
    = case t of
           VDCon _ cn _ _ sp =>
            do
              sp_value <- toList <$> traverseSnocList value sp
              -- if s is smaller or equal to an arg, then it is smaller than t
              if !(sizeCompareConArgs substs (minus fuel 1) s sp_value) then pure True
               else case (fuel, s) of
                      (S k, VDCon _ cn' _ _ sp') => do
                              -- if s is a matching DataCon, applied to same number of args,
                              -- no Unknown args, and at least one Smaller
                              if cn == cn' && length sp == length sp'
                                then (Smaller ==) <$> sizeCompareProdConArgs substs k (toList !(traverseSnocList value sp')) sp_value
                                else pure False
                      _ => pure $ False
           _ => pure False

sizeCompareConArgs _ _ s [] = pure False
sizeCompareConArgs substs fuel s (t :: ts)
    = case !(sizeCompare substs fuel s t) of
        Unknown => sizeCompareConArgs substs fuel s ts
        _ => pure True

sizeCompareApp substs fuel l@(VApp _ _ n sp _) r@(VApp _ _ n' sp' _)
 = if n == n'
     then if length sp == length sp'
             then do sp_value <- toList <$> traverseSnocList value sp
                     sp_value' <- toList <$> traverseSnocList value sp'
                     sizeCompareProdConArgs substs fuel sp_value sp_value'
             else do -- TODO: how to compare detected recursion?
                     -- It is a case like: {arg:0} vs {arg:0} {arg:1}
                     pure Same
     else do pure Unknown
sizeCompareApp _ _ _ t = pure Unknown

sizeCompareAsserted : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Substitutions -> Nat -> Maybe (Glued [<]) -> Glued [<] -> Core SizeChange
sizeCompareAsserted substs fuel (Just s) t
    = pure $ case !(sizeCompare substs fuel s t) of
        Unknown => Unknown
        _ => Smaller
sizeCompareAsserted _ _ Nothing _ = pure Unknown

addSubstitution : Name -> Glued [<] -> Substitutions -> Substitutions
addSubstitution nm val = merge $ singleton nm [<val]

expandForced : List (Glued [<], Glued [<])
               -> Substitutions -> Substitutions
expandForced [] substs = substs
-- Only useful if the equality evaluated to a bound name that we know about
expandForced ((VApp _ Bound n _ _, tm) :: fs) substs
    = expandForced fs (addSubstitution n tm substs)
expandForced (_ :: fs) substs = expandForced fs substs

data SCVar : Type where

mkvar : Int -> Value f [<]
mkvar i = vRef EmptyFC Bound (MN "scv" i)

nextVar : {auto c : Ref SCVar Int} -> Core (Value f [<])
nextVar
    = do v <- get SCVar
         put SCVar (v + 1)
         pure (mkvar v)

ForcedEqs : Type
ForcedEqs = List (Glued [<], Glued [<])

findVar : Int -> List (Glued vars, Glued vars) -> Maybe (Glued vars)
findVar i [] = Nothing
findVar i ((VApp _ Bound (MN _ i') _ _, tm) :: eqs)
    = if i == i' then Just tm else findVar i eqs
findVar i (_ :: eqs) = findVar i eqs

canonicalise : List (Glued vars, Glued vars) -> Glued vars -> Core (Glued vars)
canonicalise eqs tm@(VApp _ Bound (MN _ i) _ _)
    = case findVar i eqs of
           Nothing => pure tm
           Just val => canonicalise eqs val
canonicalise eqs (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(canonSp sp)
  where
    canonSp : Spine vars -> Core (Spine vars)
    canonSp [<] = pure [<]
    canonSp (rest :< MkSpineEntry fc c arg)
        = do rest' <- canonSp rest
             pure (rest' :< MkSpineEntry fc c (canonicalise eqs !arg))
-- for matching on types, convert to the form the case tree builder uses
canonicalise eqs (VPrimVal fc (PrT c))
    = pure $ (VTCon fc (UN (Basic $ show c)) 0 [<])
canonicalise eqs (VType fc _)
    = pure $ (VTCon fc (UN (Basic "Type")) 0 [<])
canonicalise eqs val = pure val

mutual
  findSC : {auto c : Ref Ctxt Defs} ->
           {auto v : Ref SCVar Int} ->
           Guardedness ->
           ForcedEqs ->
           List (Nat, Glued [<]) -> -- LHS args and their position
           Substitutions ->
           Glued [<] -> -- definition. No expanding to NF, we want to check
                        -- the program as written (plus tcinlines)
           Core (List SCCall)
  -- If we're Guarded and find a Delay, continue with the argument as InDelay
  findSC Guarded eqs args substs (VDelay _ LInf _ tm)
      = findSC InDelay eqs args substs tm
  findSC g eqs args substs (VBind _ _ (Lam _ _ _ _) sc)
      = findSC g eqs args substs !(sc nextVar)
  findSC g eqs args substs (VBind _ _ (Let _ erased (VAs _ UseRight (VApp _ Bound n [<] _) as) _) sc)
      = do let substs' = addSubstitution n as substs
           -- No mix the following: $ !(findSC g eqs args substs as) ++ !(findSC g eqs args substs' !(sc nextVar))
           -- because `as` came from erased, so, no actual structural decrease
           findSC g eqs args substs' !(sc nextVar)
  findSC g eqs args substs (VBind fc n b sc)
      = do v <- nextVar
           pure $ !(findSCbinder b) ++ !(findSC g eqs args substs !(sc (pure v)))
    where
        findSCbinder : Binder (Glued [<]) -> Core (List SCCall)
        findSCbinder (Let _ c val ty) = findSC g eqs args substs val
        findSCbinder _ = pure [] -- only types, no need to look
  findSC g eqs args substs (VDelay _ _ _ tm)
      = findSC g eqs args substs tm
  findSC g eqs args substs (VForce _ _ v sp)
      = do vCalls <- findSC Unguarded eqs args substs v
           spCalls <- findSCspine Unguarded eqs args substs sp
           pure (vCalls ++ spCalls)
  findSC g eqs args substs tm@(VCase fc ct c (VApp _ Bound n [<] _) scTy alts)
      = do logNF "totality.termination.sizechange" 50 "findSC VCase VApp Bound ct=\{show ct} tm" [<] tm
           altCalls <- traverse (findSCalt g eqs args substs (Just n)) alts
           pure (concat altCalls)
  findSC g eqs args substs tm@(VCase _ ct c (VApp fc Func fn sp _) scTy alts)
      = do logNF "totality.termination.sizechange" 50 "findSC VCase VApp Func ct=\{show ct} tm" [<] tm
           scCalls <- findSCAppFunc g eqs args substs fc fn sp

           altCalls <- traverse (findSCalt g eqs args substs Nothing) alts
           pure (scCalls ++ concat altCalls)

  findSC g eqs args substs tm@(VCase fc ct c sc scTy alts)
      = do logNF "totality.termination.sizechange" 50 "findSC VCase VApp ? ct=\{show ct} tm" [<] tm
           altCalls <- logDepth $ traverse (findSCalt g eqs args substs Nothing) alts
           logC "totality.termination.sizechange" 50 $ pure "findSC VCase VApp ? altCalls: \{show altCalls}"
           scCalls <- logDepth $ findSC Unguarded eqs args substs (asGlued sc)
           logC "totality.termination.sizechange" 50 $ pure "findSC VCase VApp ? scCalls: \{show scCalls}"
           pure (scCalls ++ concat altCalls)
  findSC g eqs args substs tm = do
    logNF "totality.termination.sizechange" 50 "findSC findSCapp tm g=\{show g}" [<] tm
    findSCapp g eqs args substs tm

  findSCAppFunc : {auto c : Ref Ctxt Defs} ->
                  {auto v : Ref SCVar Int} ->
                  Guardedness ->
                  ForcedEqs ->
                  List (Nat, Glued [<]) -> -- LHS args and their position
                  Substitutions ->
                  FC -> Name -> Spine [<] ->
                  Core (List SCCall)
  findSCAppFunc g eqs args substs fc fn sp = do
      let False = isAssertTotal !(getFullName fn)
        | _ => pure []

      allg <- allGuarded fn

      logC "totality.termination.sizechange" 50 $ pure "findSCAppFunc \{show !(toFullNames fn)}, g=\{show g}, allg=\{show allg}"
      -- If it has the all guarded flag, pretend it's a data constructor
      -- Otherwise just carry on as normal
      if allg
        then findSCapp g eqs args substs (VDCon fc fn 0 0 sp)
        else case g of
                -- constructor guarded and delayed, so just check the
                -- arguments
                InDelay => findSCspine Unguarded eqs args substs sp
                _ => do fn_args <- traverseSnocList value sp
                        findSCcall Unguarded eqs args substs fc fn (cast fn_args)
    where
      isAssertTotal : Name -> Bool
      isAssertTotal = (== NS builtinNS (UN $ Basic "assert_total"))

      allGuarded : Name -> Core Bool
      allGuarded n
          = do defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                    | Nothing => pure False
               pure (AllGuarded `elem` flags gdef)

  findSCapp : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
              Guardedness ->
              ForcedEqs ->
              List (Nat, Glued [<]) -> -- LHS args and their position
              Substitutions ->
              Glued [<] -> -- dealing with cases where this is an application
                           -- of some sort
              Core (List SCCall)
  findSCapp g eqs pats substs (VLocal fc _ _ sp)
      = do args <- traverseSnocList value sp
           scs <- traverseSnocList (findSC Unguarded eqs pats substs) args
           pure (concat scs)
  findSCapp g eqs pats substs (VPrimOp _ _ sp)
      = do scs <- traverse (findSC Unguarded eqs pats substs) (toList sp)
           pure (concat scs)
  findSCapp g eqs pats substs (VApp fc Bound fn sp _)
      = do args <- traverseSnocList value sp
           logC "totality.termination.sizechange" 50 $ pure "findSCapp VApp Bound \{show !(toFullNames fn)}"
           for_ (toList args) $ \a =>
             logNF "totality.termination.sizechange" 50 "findSCapp VApp Bound arg" [<] a
           scs <- traverseSnocList (findSC Unguarded eqs pats substs) args
           pure (concat scs)
  findSCapp g eqs pats substs (VApp fc Func fn sp _) = findSCAppFunc g eqs pats substs fc fn sp
  -- If we're InDelay and find a constructor (or a function call which is
  -- guaranteed to return a constructor; AllGuarded set), continue as InDelay
  findSCapp InDelay eqs pats substs (VDCon fc n t a sp)
      = findSCspine InDelay eqs pats substs sp
  findSCapp Guarded eqs pats substs (VDCon fc n t a sp)
      = do defs <- get Ctxt
           findSCcall Guarded eqs pats substs fc n (toList !(traverseSnocList value sp))
  findSCapp Toplevel eqs pats substs (VDCon fc n t a sp)
      = do defs <- get Ctxt
           findSCcall Guarded eqs pats substs fc n (toList !(traverseSnocList value sp))
  findSCapp g eqs pats substs tm = pure [] -- not an application (TODO: VTCon)


  findSCscope : {auto c : Ref Ctxt Defs} ->
                {auto v : Ref SCVar Int} ->
                Guardedness ->
                ForcedEqs ->
                List (Nat, Glued [<]) -> -- LHS args and their position
                Substitutions ->
                Maybe Name -> -- variable we're splitting on (if it is a variable)
                FC -> Glued [<] ->
                (args : _) -> VCaseScope args [<] -> -- case alternative
                Core (List SCCall)
  findSCscope g eqs args substs var fc pat [<] sc
     = do (eqsc, rhs) <- sc
          logC "totality.termination.sizechange" 10 $
              (do tms <- traverse (\ (gx, gy) =>
                              pure (!(toFullNames !(quote [<] gx)),
                                    !(toFullNames !(quote [<] gy)))) eqsc
                  teqs <- traverse (\ (gx, gy) =>
                              pure (!(toFullNames !(quote [<] gx)),
                                    !(toFullNames !(quote [<] gy)))) eqs
                  pure ("Force equalities eqsc=\{show tms}, eqs=\{show teqs}"))
          let eqs' = eqsc ++ eqs
          logC "totality.termination.sizechange" 10 $ do
            pat <- toFullNames !(quote [<] pat)
            pure "findSCscope addSubstitution for var=\{show !(toFullNames var)}, pat=\{show pat}"
          let substs' = maybe substs (\v => addSubstitution v pat substs) var
          logC "totality.termination.sizechange" 50 $ do
            args <- traverse (\ (a, b) => pure (a, !(toFullNames !(quote [<] b)))) args
            pure "findSCscope canonicalise args=\{show args}"
          args'' <- traverse (\ (n, arg) => pure (n, !(canonicalise eqs' arg))) args
          logC "totality.termination.sizechange" 50 $ do
            args'' <- traverse (\ (a, b) => pure (a, !(toFullNames !(quote [<] b)))) args''
            pure "findSCscope canonicalised args=\{show args''}"
          logNF "totality.termination.sizechange" 10 "RHS var=\{show !(toFullNames var)}" [<] rhs
          logDepth $ findSC g eqs' args'' substs' rhs
  findSCscope g eqs args substs var fc pat (cargs :< (c, xn)) sc
     = do varg <- nextVar
          pat' <- the (Core (Glued [<])) $ case pat of
                    VDCon vfc n t a sp =>
                        pure (VDCon vfc n t a (sp :< MkSpineEntry fc c (pure varg)))
                    _ => throw (InternalError "Not a data constructor in findSCscope")
          logNF "totality.termination.sizechange" 10 "findSCscope varg=\{show varg} xn=\{show xn} pat" [<] pat
          logNF "totality.termination.sizechange" 10 "findSCscope varg=\{show varg} xn=\{show xn} pat'" [<] pat'
          findSCscope g eqs args substs var fc pat' cargs (sc (pure varg))

  findSCalt : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
              Guardedness ->
              ForcedEqs ->
              List (Nat, Glued [<]) -> -- LHS args and their position
              Substitutions ->
              Maybe Name -> -- variable we're splitting on (if it is a variable)
              VCaseAlt [<] -> -- case alternative
              Core (List SCCall)
  findSCalt g eqs args substs var (VConCase fc n t cargs sc)
      = findSCscope g eqs args substs var fc (VDCon fc n t (length cargs) [<]) _ sc
  findSCalt g eqs args substs var (VDelayCase fc ty arg tm)
      = do targ <- nextVar
           varg <- nextVar
           let pat = VDelay fc LUnknown targ varg
           (eqs, rhs) <- tm (pure targ) (pure varg)
           logDepth $ findSC g eqs args (expandForced eqs
                       (maybe substs
                               (\v => addSubstitution v pat substs) var))
                    rhs
  findSCalt g eqs args substs var (VConstCase fc c tm)
      = logDepth $ findSC g eqs args (maybe substs
                         (\v => addSubstitution v (VPrimVal fc c) substs) var)
                 tm
  findSCalt g eqs args substs _ (VDefaultCase fc tm) = logDepth $ findSC g eqs args substs tm


  findSCspine : {auto c : Ref Ctxt Defs} ->
           {auto v : Ref SCVar Int} ->
           Guardedness ->
           ForcedEqs ->
           List (Nat, Glued [<]) -> -- LHS args and their position
           Substitutions ->
           Spine [<] ->
           Core (List SCCall)
  findSCspine g eqs pats substs [<] = pure []
  findSCspine g eqs pats substs (sp :< e)
      = do vCalls <- findSC g eqs pats substs !(value e)
           spCalls <- findSCspine g eqs pats substs sp
           pure (vCalls ++ spCalls)



  -- if the argument is an 'assert_smaller', return the thing it's smaller than
  asserted : ForcedEqs -> Name -> Glued [<] -> Core (Maybe (Glued [<]))
  asserted eqs aSmaller (VApp _ nt fn [<_, _, e, _] _)
       = if fn == aSmaller
            then Just <$> canonicalise eqs !(value e)
            else pure Nothing
  asserted _ _ _ = pure Nothing

  -- Calculate the size change for the given argument.
  -- i.e., return the size relationship of the given argument with an entry
  -- in 'pats'; the position in 'pats' and the size change.
  -- Nothing if there is no relation with any of them.
  mkChange : {auto c : Ref Ctxt Defs} ->
             ForcedEqs ->
             Name ->
             Substitutions ->
             (pats : List (Nat, Glued [<])) ->
             (arg : Glued [<]) ->
             Core (List SizeChange)
  mkChange eqs aSmaller substs pats arg
    = do defs <- get Ctxt
         let fuel = defs.options.elabDirectives.totalLimit
         res <- traverse (\(n, p) => pure (n, !(plusLazy (sizeCompareAsserted substs fuel !(asserted eqs aSmaller arg) p) (sizeCompare substs fuel arg p)))) pats
         let squashed = fromListWith (|+|) res
         pure $ toList squashed

  findSCcall : {auto c : Ref Ctxt Defs} ->
               {auto v : Ref SCVar Int} ->
               Guardedness ->
               ForcedEqs ->
               List (Nat, Glued [<]) ->
               Substitutions ->
               FC -> Name -> List (Glued [<]) ->
               Core (List SCCall)
  findSCcall g eqs pats substs fc fn_in args
          -- Under 'assert_total' we assume that all calls are fine, so leave
          -- the size change list empty
        = do args <- traverse (canonicalise eqs) args
             substs <- traverseNameMap (const $ traverseSnocList $ canonicalise eqs) substs
             defs <- get Ctxt
             fn <- getFullName fn_in
             logC "totality.termination.sizechange" 10 $ do pure "Looking under \{show fn}"
             aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
             logC "totality.termination.sizechange" 20 $
                 do under <- traverse (\ (n, t) =>
                                pure (n, !(toFullNames !(quote [<] t)))) pats
                    targs <- traverse (\t => toFullNames !(quote [<] t)) args
                    pure ("Under " ++ show under ++ "\n" ++ "Args " ++ show targs)
             scs <- traverse (\x => logDepth $ findSC g eqs pats substs x) args
             pure ([MkSCCall fn
                   (fromListList
                        !(traverse (mkChange eqs aSmaller substs pats) args))
                   fc] ++ concat scs)

findSCTop : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
            Nat -> List (Nat, Glued [<]) -> Glued [<] -> Core (List SCCall)
findSCTop i args (VBind _ _ (Lam _ _ _ _) sc)
    = do arg <- nextVar
         findSCTop (i + 1) ((i, arg) :: args) !(sc $ pure arg)
findSCTop i args def = findSC Toplevel [] (reverse args) empty def

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ tm _ pats)
   = do logTerm "totality.termination.sizechange" 5 "From term" tm
        logC "totality.termination.sizechange" 5 $ pure "From pats \{show !(toFullNames pats)}"
        ntm <- nfTotality [<] tm
        logNF "totality.termination.sizechange" 5 "From tree" [<] ntm
        v <- newRef SCVar 0
        sc <- findSCTop 0 [] ntm
        pure $ nub sc
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do logC "totality.termination.sizechange" 5 $ do pure $ "Calculating Size Change: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         r <- getSC defs (definition def)
         log "totality.termination.sizechange" 5 $ "Calculated: " ++ show r
         pure r
