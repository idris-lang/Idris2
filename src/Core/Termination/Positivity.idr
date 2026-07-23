module Core.Termination.Positivity

import Core.Context.Log
import Core.Env
import Core.Evaluate
import Core.Evaluate.Value
import Core.Evaluate.Normalise
import Core.Evaluate.Expand

import Core.Termination.References

import Data.String

import Libraries.Data.NatSet

%default covering

isAssertTotal : Ref Ctxt Defs => Name -> Core Bool
isAssertTotal fn_in =
  do fn <- getFullName fn_in
     pure (fn == NS builtinNS (UN $ Basic "assert_total"))

nameIn : {auto c : Ref Ctxt Defs} ->
         List Name -> NF [<] -> Core Bool
nameIn tyns (VBind fc x b sc)
    = if !(nameIn tyns !(expand (binderType b)))
         then pure True
         else do sc' <- sc (pure (vRef fc Bound (MN ("NAMEIN_" ++ show x) 0)))
                 nameIn tyns !(expand sc')
nameIn tyns (VApp _ nt n args _)
    = do False <- isAssertTotal n
           | True => pure False
         Core.Core.anyM (nameIn tyns) (cast !(traverseSnocList spineVal args))
nameIn tyns (VTCon _ n _ args)
    = if n `elem` tyns
         then pure True
         else do args' <- traverseSnocList spineVal args
                 Core.Core.anyM (nameIn tyns) (cast args')
nameIn tyns (VDCon _ n _ _ args)
    = Core.Core.anyM (nameIn tyns)
           (cast !(traverseSnocList spineVal args))
nameIn tyns (VDelayed fc lr ty) = nameIn tyns !(expand ty)
nameIn tyns (VDelay fc lr ty tm) = nameIn tyns !(expand tm)
nameIn tyns _ = pure False

-- Check an argument type doesn't contain a negative occurrence of any of
-- the given type names
posArg  : {auto c : Ref Ctxt Defs} ->
          List Name -> NF [<] -> Core Terminating

posArgs : {auto c : Ref Ctxt Defs} ->
          List Name -> SnocList (Glued [<]) -> Core Terminating
posArgs tyn [<] = pure IsTerminating
posArgs tyn (xs :< x)
  = do xNF <- expand x
       logNF "totality.positivity" 50 "Checking parameter for positivity" Env.empty xNF
       IsTerminating <- posArg tyn xNF
          | err => pure err
       posArgs tyn xs

-- a tyn can only appear in the parameter positions of
-- tc; report positivity failure if it appears anywhere else
posArg tyns nf@(VTCon loc tc _ args) =
  do logNF "totality.positivity" 50 "Found a type constructor" Env.empty nf
     defs <- get Ctxt
     testargs <- case !(lookupDefExact tc (gamma defs)) of
                    Just (TCon _ params _ _ _ _ _) => do
                         logC "totality.positivity" 50 $
                           do pure $ unwords [show tc, "has", show (NatSet.size params), "parameters"]
                         pure $ NatSet.partition params !(traverseSnocList value args)
                    _ => throw (GenericMsg loc (show tc ++ " not a data type"))
     let (params, indices) = testargs
     False <- Core.Core.anyM (nameIn tyns) (cast !(traverseSnocList expand indices))
       | True => pure (NotTerminating NotStrictlyPositive)
     posArgs tyns params
-- a tyn can not appear as part of ty
posArg tyns nf@(VBind fc x (Pi _ _ e ty) sc)
  = do logNF "totality.positivity" 50 "Found a Pi-type" Env.empty nf
       if !(nameIn tyns !(expand ty))
         then pure (NotTerminating NotStrictlyPositive)
         else do sc' <- sc (pure (vRef fc Bound (MN ("POSCHECK_" ++ show x) 1)))
                 posArg tyns !(expand sc')
posArg tyns nf@(VApp _ _ n args _)
    = do False <- isAssertTotal n
           | True => do logNF "totality.positivity" 50 "Trusting an assertion" Env.empty nf
                        pure IsTerminating
         logNF "totality.positivity" 50 "Found an application" Env.empty nf
         args <- traverseSnocList spineVal args
         pure $ if !(Core.Core.anyM (nameIn tyns) (cast args))
           then NotTerminating NotStrictlyPositive
           else IsTerminating
posArg tyn (VDelayed _ _ ty) = posArg tyn !(expand ty)
posArg tyn nf
  = do logNF "totality.positivity" 50 "Reached the catchall" Env.empty nf
       pure IsTerminating

checkPosArgs : {auto c : Ref Ctxt Defs} ->
               List Name -> NF [<] -> Core Terminating
checkPosArgs tyns (VBind fc x (Pi _ _ e ty) sc)
    = case !(posArg tyns !(expand ty)) of
           IsTerminating =>
               do let nm = vRef fc Bound (MN ("POSCHECK_" ++ show x) 0)
                  checkPosArgs tyns !(expand !(sc (pure nm)))
           bad => pure bad
checkPosArgs tyns nf
  = do logNF "totality.positivity" 50 "Giving up on non-Pi type" Env.empty nf
       pure IsTerminating

checkCon : {auto c : Ref Ctxt Defs} ->
           List Name -> Name -> Core Terminating
checkCon tyns cn
    = do defs <- get Ctxt
         case !(lookupTyExact cn (gamma defs)) of
           Nothing => do log "totality.positivity" 20 $
                           "Couldn't find constructor " ++ show cn
                         pure Unchecked
           Just ty =>
             case !(totRefsIn defs ty) of
                IsTerminating =>
                  do tyNF <- nf Env.empty ty
                     logNF "totality.positivity" 20 "Checking the type " [<] tyNF
                     checkPosArgs tyns !(expand tyNF)
                bad => pure bad

checkData : {auto c : Ref Ctxt Defs} ->
            List Name -> List Name -> Core Terminating
checkData tyns [] = pure IsTerminating
checkData tyns (c :: cs)
    = do log "totality.positivity" 40 $
           "Checking positivity of constructor " ++ show c
         case !(checkCon tyns c) of
           IsTerminating => checkData tyns cs
           bad => pure bad

blockingAssertTotal : {auto c : Ref Ctxt Defs} -> FC -> Core a -> Core a
blockingAssertTotal loc ma
  = do defs <- get Ctxt
       let at = NS builtinNS (UN $ Basic "assert_total")
       Just _ <- lookupCtxtExact at (gamma defs)
         | Nothing => ma
       setVisibility loc at Private
       a <- ma
       setVisibility loc at Public
       pure a

-- Calculate whether a type satisfies the strict positivity condition, and
-- return whether it's terminating, along with its data constructors
export
calcPositive : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Core (Terminating, List Name)
calcPositive loc n
    = do defs <- get Ctxt
         logC "totality.positivity" 6 $ do pure $ "Calculating positivity: \{show !(toFullNames n)}"
         case !(lookupDefTyExact n (gamma defs)) of
              Just (TCon _ _ _ _ tns dcons _, ty) =>
                  let dcons = fromMaybe [] dcons in
                  case !(totRefsIn defs ty) of
                       IsTerminating =>
                            do logC "totality.positivity" 30 $
                                 do pure $ "Now checking constructors of \{show !(toFullNames n)}"
                               t <- blockingAssertTotal loc $ checkData (n :: tns) dcons
                               pure (t , dcons)
                       bad => pure (bad, dcons)
              Just _ => throw (GenericMsg loc (show n ++ " not a data type"))
              Nothing => undefinedName loc n
