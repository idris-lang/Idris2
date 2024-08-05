module Core.Termination.Positivity

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Value

import Core.Termination.References

import Data.String

import Libraries.Data.NameMap

%default covering

isAssertTotal : Ref Ctxt Defs => NHead{} -> Core Bool
isAssertTotal (NRef _ fn_in) =
  do fn <- getFullName fn_in
     pure (fn == NS builtinNS (UN $ Basic "assert_total"))
isAssertTotal _ = pure False

nameIn : {auto c : Ref Ctxt Defs} ->
         Defs -> List Name -> NF SLNil -> Core Bool
nameIn defs tyns (NBind fc x b sc)
    = if !(nameIn defs tyns !(evalClosure defs (binderType b)))
         then pure True
         else do let nm = Ref fc Bound (MN ("NAMEIN_" ++ show x) 0)
                 let arg = toClosure defaultOpts [] nm
                 sc' <- sc defs arg
                 nameIn defs tyns sc'
nameIn defs tyns (NApp _ nh args)
    = do False <- isAssertTotal nh
           | True => pure False
         anyM (nameIn defs tyns)
           !(traverse (evalClosure defs . snd) (toList args))
nameIn defs tyns (NTCon _ n _ _ args)
    = if n `elem` tyns
         then pure True
         else do args' <- traverse (evalClosure defs . snd) (toList args)
                 anyM (nameIn defs tyns) args'
nameIn defs tyns (NDCon _ n _ _ args)
    = anyM (nameIn defs tyns)
           !(traverse (evalClosure defs . snd) (toList args))
nameIn defs tyns (NDelayed fc lr ty) = nameIn defs tyns ty
nameIn defs tyns _ = pure False

-- Check an argument type doesn't contain a negative occurrence of any of
-- the given type names
posArg  : {auto c : Ref Ctxt Defs} ->
          Defs -> List Name -> NF SLNil -> Core Terminating

posArgs : {auto c : Ref Ctxt Defs} ->
          Defs -> List Name -> List (Closure SLNil) -> Core Terminating
posArgs defs tyn [] = pure IsTerminating
posArgs defs tyn (x :: xs)
  = do xNF <- evalClosure defs x
       logNF "totality.positivity" 50 "Checking parameter for positivity" [] xNF
       IsTerminating <- posArg defs tyn xNF
          | err => pure err
       posArgs defs tyn xs

-- a tyn can only appear in the parameter positions of
-- tc; report positivity failure if it appears anywhere else
posArg defs tyns nf@(NTCon loc tc _ _ args) =
  do logNF "totality.positivity" 50 "Found a type constructor" [] nf
     testargs <- case !(lookupDefExact tc (gamma defs)) of
                    Just (TCon _ _ params _ _ _ _ _) => do
                         logC "totality.positivity" 50 $
                           do pure $ unwords [show tc, "has", show (length params), "parameters"]
                         pure $ splitParams 0 params (map snd (toList args))
                    _ => throw (GenericMsg loc (show tc ++ " not a data type"))
     let (params, indices) = testargs
     False <- anyM (nameIn defs tyns) !(traverse (evalClosure defs) indices)
       | True => pure (NotTerminating NotStrictlyPositive)
     posArgs defs tyns params
  where
    splitParams : Nat -> List Nat -> List (Closure SLNil) ->
        ( List (Closure SLNil) -- parameters (to be checked for strict positivity)
        , List (Closure SLNil) -- indices    (to be checked for no mention at all)
        )
    splitParams i ps [] = ([], [])
    splitParams i ps (x :: xs)
        = if i `elem` ps
             then mapFst (x ::) (splitParams (S i) ps xs)
             else mapSnd (x ::) (splitParams (S i) ps xs)
-- a tyn can not appear as part of ty
posArg defs tyns nf@(NBind fc x (Pi _ _ e ty) sc)
  = do logNF "totality.positivity" 50 "Found a Pi-type" [] nf
       if !(nameIn defs tyns !(evalClosure defs ty))
         then pure (NotTerminating NotStrictlyPositive)
         else do let nm = Ref fc Bound (MN ("POSCHECK_" ++ show x) 1)
                 let arg = toClosure defaultOpts [] nm
                 sc' <- sc defs arg
                 posArg defs tyns sc'
posArg defs tyns nf@(NApp fc nh args)
    = do False <- isAssertTotal nh
           | True => do logNF "totality.positivity" 50 "Trusting an assertion" [] nf
                        pure IsTerminating
         logNF "totality.positivity" 50 "Found an application" [] nf
         args <- traverse (evalClosure defs . snd) (toList args)
         pure $ if !(anyM (nameIn defs tyns) args)
           then NotTerminating NotStrictlyPositive
           else IsTerminating
posArg defs tyn (NDelayed fc lr ty) = posArg defs tyn ty
posArg defs tyn nf
  = do logNF "totality.positivity" 50 "Reached the catchall" [] nf
       pure IsTerminating

checkPosArgs : {auto c : Ref Ctxt Defs} ->
               Defs -> List Name -> NF SLNil -> Core Terminating
checkPosArgs defs tyns (NBind fc x (Pi _ _ e ty) sc)
    = case !(posArg defs tyns !(evalClosure defs ty)) of
           IsTerminating =>
               do let nm = Ref fc Bound (MN ("POSCHECK_" ++ show x) 0)
                  let arg = toClosure defaultOpts [] nm
                  checkPosArgs defs tyns !(sc defs arg)
           bad => pure bad
checkPosArgs defs tyns nf
  = do logNF "totality.positivity" 50 "Giving up on non-Pi type" [] nf
       pure IsTerminating

checkCon : {auto c : Ref Ctxt Defs} ->
           Defs -> List Name -> Name -> Core Terminating
checkCon defs tyns cn
    = case !(lookupTyExact cn (gamma defs)) of
        Nothing => do log "totality.positivity" 20 $
                        "Couldn't find constructor " ++ show cn
                      pure Unchecked
        Just ty =>
          case !(totRefsIn defs ty) of
            IsTerminating =>
              do tyNF <- nf defs [] ty
                 logNF "totality.positivity" 20 "Checking the type " [] tyNF
                 checkPosArgs defs tyns tyNF
            bad => pure bad

checkData : {auto c : Ref Ctxt Defs} ->
            Defs -> List Name -> List Name -> Core Terminating
checkData defs tyns [] = pure IsTerminating
checkData defs tyns (c :: cs)
    = do log "totality.positivity" 40 $
           "Checking positivity of constructor " ++ show c
         case !(checkCon defs tyns c) of
           IsTerminating => checkData defs tyns cs
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
         logC "totality.positivity" 6 $ do pure $ "Calculating positivity: " ++ show !(toFullNames n)
         case !(lookupDefTyExact n (gamma defs)) of
              Just (TCon _ _ _ _ _ tns dcons _, ty) =>
                  let dcons = fromMaybe [] dcons in
                  case !(totRefsIn defs ty) of
                       IsTerminating =>
                            do log "totality.positivity" 30 $
                                 "Now checking constructors of " ++ show !(toFullNames n)
                               t <- blockingAssertTotal loc $ checkData defs (n :: tns) dcons
                               pure (t , dcons)
                       bad => pure (bad, dcons)
              Just _ => throw (GenericMsg loc (show n ++ " not a data type"))
              Nothing => undefinedName loc n
