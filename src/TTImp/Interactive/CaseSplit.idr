module TTImp.Interactive.CaseSplit

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.UnifyState
import Core.Value

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.ProcessDef
import TTImp.ProcessDecls
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

import Data.List
import Libraries.Data.NameMap

%default covering

-- The result of a request to case split is a list of string updates, i.e. edits
-- on the clause in the source file, which an interactive editor can deal with
-- however it sees fit. 'Valid' means that the result will type check,
-- 'Impossible' means that the result will be a valid 'impossible' case
public export
data ClauseUpdate : Type where
     Valid : RawImp -> List (Name, RawImp) -> ClauseUpdate
     Impossible : RawImp -> ClauseUpdate
     Invalid : ClauseUpdate

export
Show ClauseUpdate where
  show (Valid lhs updates) = "Valid: " ++ show lhs ++ "\n" ++ "Updates: " ++ show updates
  show (Impossible lhs) = "Impossible: " ++ show lhs
  show Invalid = "Invalid"

public export
data SplitError : Type where
     NoValidSplit : SplitError -- None of the splits either type check, or fail
                               -- in a way which is valid as an 'impossible' case
     CantSplitThis : Name -> String -> SplitError -- Request to split was not on a splittable variable
     CantFindLHS : SplitError -- Can't find any clause to split

export
Show SplitError where
  show NoValidSplit = "No valid case splits"
  show (CantSplitThis n r) = "Can't split on " ++ show n ++ " (" ++ r ++ ")"
  show CantFindLHS = "No clause to split here"

public export
data SplitResult : Type -> Type where
     SplitFail : SplitError -> SplitResult a
     OK : a -> SplitResult a

export
Show a => Show (SplitResult a) where
  show (SplitFail err) = "Split error: " ++ show err
  show (OK res) = "OK: " ++ show res

findTyName : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Defs -> Env Term vars -> Name -> Term vars ->
             Core (Maybe Name)
findTyName defs env n (Bind _ x b@(PVar _ c p ty) sc)
      -- Take the first one, which is the most recently bound
    = if n == x
         then do tynf <- nf defs env ty
                 case tynf of
                      NTCon _ tyn _ _ _ => pure $ Just tyn
                      _ => pure Nothing
         else findTyName defs (b :: env) n sc
findTyName defs env n (Bind _ x b sc) = findTyName defs (b :: env) n sc
findTyName _ _ _ _ = pure Nothing

getDefining : Term vars -> Maybe Name
getDefining (Bind _ _ _ sc) = getDefining sc
getDefining tm
    = case getFn tm of
           Ref _ _ fn => Just fn
           _ => Nothing

-- For the name on the lhs, return the function name being defined, the
-- type name, and the possible constructors.
findCons : {auto c : Ref Ctxt Defs} ->
           Name -> Term [] -> Core (SplitResult (Name, Name, List Name))
findCons n lhs
    = case getDefining lhs of
           Nothing => pure (SplitFail
                            (CantSplitThis n "Can't find function name on LHS"))
           Just fn =>
              do defs <- get Ctxt
                 case !(findTyName defs [] n lhs) of
                      Nothing => pure (SplitFail (CantSplitThis n
                                         ("Can't find type of " ++ show n ++ " in LHS")))
                      Just tyn =>
                          do Just (TCon _ _ _ _ _ _ cons _) <-
                                      lookupDefExact tyn (gamma defs)
                                | res => pure (SplitFail
                                            (CantSplitThis n
                                               ("Not a type constructor " ++
                                                  show res)))
                             pure (OK (fn, !(toFullNames tyn),
                                           !(traverse toFullNames cons)))

findAllVars : Term vars -> List Name
findAllVars (Bind _ x (PVar _ _ _ _) sc)
    = x :: findAllVars sc
findAllVars (Bind _ x (Let _ _ _ _) sc)
    = x :: findAllVars sc
findAllVars (Bind _ x (PLet _ _ _ _) sc)
    = x :: findAllVars sc
findAllVars _ = []

unique : List String -> List String -> Int -> List Name -> String
unique [] supply suff usedns = unique supply supply (suff + 1) usedns
unique (str :: next) supply suff usedns
    = let var = mkVarN str suff in
          if UN var `elem` usedns
             then unique next supply suff usedns
             else var
  where
    mkVarN : String -> Int -> String
    mkVarN x 0 = x
    mkVarN x i = x ++ show i

defaultNames : List String
defaultNames = ["x", "y", "z", "w", "v", "s", "t", "u"]

export
getArgName : {auto c : Ref Ctxt Defs} ->
             Defs -> Name ->
             List Name -> -- explicitly bound names (possibly coming later),
                          -- so we don't invent a default
                          -- name that duplicates it
             List Name -> -- names bound so far
             NF vars -> Core String
getArgName defs x bound allvars ty
    = do defnames <- findNames ty
         pure $ getName x defnames allvars
  where
    lookupName : Name -> List (Name, a) -> Core (Maybe a)
    lookupName n [] = pure Nothing
    lookupName n ((n', t) :: ts)
        = if !(getFullName n) == !(getFullName n')
             then pure (Just t)
             else lookupName n ts

    notBound : String -> Bool
    notBound x = not $ UN x `elem` bound

    findNames : NF vars -> Core (List String)
    findNames (NBind _ x (Pi _ _ _ _) _)
        = pure (filter notBound ["f", "g"])
    findNames (NTCon _ n _ _ _)
        = case !(lookupName n (NameMap.toList (namedirectives defs))) of
               Nothing => pure (filter notBound defaultNames)
               Just ns => pure (filter notBound ns)
    findNames ty = pure (filter notBound defaultNames)

    getName : Name -> List String -> List Name -> String
    getName (UN n) defs used = unique (n :: defs) (n :: defs) 0 used
    getName _ defs used = unique defs defs 0 used

export
getArgNames : {auto c : Ref Ctxt Defs} ->
              Defs -> List Name -> List Name -> Env Term vars -> NF vars ->
              Core (List String)
getArgNames defs bound allvars env (NBind fc x (Pi _ _ p ty) sc)
    = do ns <- case p of
                    Explicit => pure [!(getArgName defs x bound allvars ty)]
                    _ => pure []
         sc' <- sc defs (toClosure defaultOpts env (Erased fc False))
         pure $ ns ++ !(getArgNames defs bound (map UN ns ++ allvars) env sc')
getArgNames defs bound allvars env val = pure []

export
explicitlyBound : Defs -> NF [] -> Core (List Name)
explicitlyBound defs (NBind fc x (Pi _ _ _ _) sc)
    = pure $ x :: !(explicitlyBound defs
                    !(sc defs (toClosure defaultOpts [] (Erased fc False))))
explicitlyBound defs _ = pure []

export
getEnvArgNames : {auto c : Ref Ctxt Defs} ->
                 Defs -> Nat -> NF [] -> Core (List String)
getEnvArgNames defs Z sc = getArgNames defs !(explicitlyBound defs sc) [] [] sc
getEnvArgNames defs (S k) (NBind fc n _ sc)
    = getEnvArgNames defs k !(sc defs (toClosure defaultOpts [] (Erased fc False)))
getEnvArgNames defs n ty = pure []

expandCon : {auto c : Ref Ctxt Defs} ->
            FC -> List Name -> Name -> Core RawImp
expandCon fc usedvars con
    = do defs <- get Ctxt
         Just ty <- lookupTyExact con (gamma defs)
              | Nothing => undefinedName fc con
         pure (apply (IVar fc con)
                (map (IBindVar fc)
                     !(getArgNames defs [] usedvars []
                                   !(nf defs [] ty))))

updateArg : {auto c : Ref Ctxt Defs} ->
            List Name -> -- all the variable names
            (var : Name) -> (con : Name) ->
            RawImp -> Core RawImp
updateArg allvars var con (IVar fc n)
    = if n `elem` allvars
         then if n == var
                 then expandCon fc (filter (/= n) allvars) con
                 else pure $ Implicit fc True
         else pure $ IVar fc n
updateArg allvars var con (IApp fc f a)
    = pure $ IApp fc !(updateArg allvars var con f)
                     !(updateArg allvars var con a)
updateArg allvars var con (IAutoApp fc f a)
    = pure $ IAutoApp fc !(updateArg allvars var con f)
                     !(updateArg allvars var con a)
updateArg allvars var con (INamedApp fc f n a)
    = pure $ INamedApp fc !(updateArg allvars var con f) n
                          !(updateArg allvars var con a)
updateArg allvars var con (IAs fc nameFC s n p)
    = updateArg allvars var con p
updateArg allvars var con tm = pure $ Implicit (getFC tm) True

data ArgType
    = Explicit FC RawImp
    | Auto     FC RawImp
    | Named    FC Name RawImp

update : {auto c : Ref Ctxt Defs} ->
         List Name -> -- all the variable names
         (var : Name) -> (con : Name) ->
         ArgType -> Core ArgType
update allvars var con (Explicit fc arg)
    = pure $ Explicit fc !(updateArg allvars var con arg)
update allvars var con (Auto fc arg)
    = pure $ Auto fc !(updateArg allvars var con arg)
update allvars var con (Named fc n arg)
    = pure $ Named fc n !(updateArg allvars var con arg)

getFnArgs : RawImp -> List ArgType -> (RawImp, List ArgType)
getFnArgs (IApp fc tm a) args
    = getFnArgs tm (Explicit fc a :: args)
getFnArgs (IAutoApp fc tm a) args
    = getFnArgs tm (Auto fc a :: args)
getFnArgs (INamedApp fc tm n a) args
    = getFnArgs tm (Named fc n a :: args)
getFnArgs tm args = (tm, args)

apply : RawImp -> List ArgType -> RawImp
apply f (Explicit fc a :: args) = apply (IApp fc f a) args
apply f (Auto fc a :: args) = apply (IAutoApp fc f a) args
apply f (Named fc n a :: args) = apply (INamedApp fc f n a) args
apply f [] = f

-- Return a new LHS to check, replacing 'var' with an application of 'con'
-- Also replace any variables with '_' to allow elaboration to
-- expand them
newLHS : {auto c : Ref Ctxt Defs} ->
         FC ->
         Nat -> -- previous environment length; leave these alone
         List Name -> -- all the variable names
         (var : Name) -> (con : Name) ->
         RawImp -> Core RawImp
newLHS fc envlen allvars var con tm
    = do let (f, args) = getFnArgs tm []
         let keep = map (const (Explicit fc (Implicit fc True)))
                        (take envlen args)
         let ups = drop envlen args
         ups' <- traverse (update allvars var con) ups
         pure $ apply f (keep ++ ups')

record Updates where
  constructor MkUpdates
  namemap : List (Name, Name)
  updates : List (Name, RawImp)

data UPD : Type where

recordUpdate : {auto u : Ref UPD Updates} ->
               FC -> Name -> RawImp -> Core ()
recordUpdate fc n tm
    = do u <- get UPD
         let nupdates = map (\x => (fst x, IVar fc (snd x))) (namemap u)
         put UPD (record { updates $= ((n, substNames [] nupdates tm) ::) } u)

findUpdates : {auto u : Ref UPD Updates} ->
              Defs -> RawImp -> RawImp -> Core ()
findUpdates defs (IVar fc n) (IVar _ n')
    = case !(lookupTyExact n' (gamma defs)) of
           Just _ => recordUpdate fc n (IVar fc n')
           Nothing =>
              do u <- get UPD
                 case lookup n' (namemap u) of
                      Nothing => put UPD (record { namemap $= ((n', n) ::) } u)
                      Just nm => put UPD (record { updates $= ((n, IVar fc nm) ::) } u)
findUpdates defs (IVar fc n) tm = recordUpdate fc n tm
findUpdates defs (IApp _ f a) (IApp _ f' a')
    = do findUpdates defs f f'
         findUpdates defs a a'
findUpdates defs (IAutoApp _ f a) (IAutoApp _ f' a')
    = do findUpdates defs f f'
         findUpdates defs a a'
findUpdates defs (IAutoApp _ f a) f'
    = findUpdates defs f f'
findUpdates defs f (IAutoApp _ f' a)
    = findUpdates defs f f'
findUpdates defs (INamedApp _ f _ a) (INamedApp _ f' _ a')
    = do findUpdates defs f f'
         findUpdates defs a a'
findUpdates defs (INamedApp _ f _ a) f' = findUpdates defs f f'
findUpdates defs f (INamedApp _ f' _ a) = findUpdates defs f f'
findUpdates defs (IAs _ _ _ _ f) f' = findUpdates defs f f'
findUpdates defs f (IAs _ _ _ _ f') = findUpdates defs f f'
findUpdates _ _ _ = pure ()

getUpdates : Defs -> RawImp -> RawImp -> Core (List (Name, RawImp))
getUpdates defs orig updated
    = do u <- newRef UPD (MkUpdates [] [])
         findUpdates defs orig updated
         pure (updates !(get UPD))

mkCase : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         Int -> RawImp -> RawImp -> Core ClauseUpdate
mkCase {c} {u} fn orig lhs_raw
    = do m <- newRef MD initMetadata
         defs <- get Ctxt
         ust <- get UST
         catch
           (do
               -- Fixes Issue #74. The problem is that if the function is defined in a sub module,
               -- then the current namespace (accessed by calling getNS) differs from the function
               -- namespace, therefore it is not considered visible by TTImp.Elab.App.checkVisibleNS
               setAllPublic True

               -- Use 'Rig0' since it might be a type level function, or it might
               -- be an erased name in a case block (which will be bound elsewhere
               -- once split and turned into a pattern)
               (lhs, _) <- elabTerm {c} {m} {u}
                                    fn (InLHS erased) [] (MkNested [])
                                    [] (IBindHere (getFC lhs_raw) PATTERN lhs_raw)
                                    Nothing
               -- Revert all public back to false
               setAllPublic False
               put Ctxt defs -- reset the context, we don't want any updates
               put UST ust
               lhs' <- unelabNoSugar [] lhs

               log "interaction.casesplit" 3 $ "Original LHS: " ++ show orig
               log "interaction.casesplit" 3 $ "New LHS: " ++ show lhs'

               pure (Valid lhs' !(getUpdates defs orig lhs')))
           (\err =>
               do put Ctxt defs
                  put UST ust
                  case err of
                       WhenUnifying _ env l r err
                          => if !(impossibleOK defs !(nf defs env l)
                                                    !(nf defs env r))
                                then pure (Impossible lhs_raw)
                                else pure Invalid
                       _ => pure Invalid)

substLets : {vars : _} ->
            Term vars -> Term vars
substLets (Bind _ n (Let _ c val ty) sc) = substLets (subst val sc)
substLets (Bind _ n (PLet _ c val ty) sc) = substLets (subst val sc)
substLets (Bind fc n b sc) = Bind fc n b (substLets sc)
substLets tm = tm

combine : List ClauseUpdate -> List ClauseUpdate ->
          SplitResult (List ClauseUpdate)
combine [] [] = SplitFail NoValidSplit
combine [] acc = OK (reverse acc)
combine (Invalid :: xs) acc = combine xs acc
combine (x :: xs) acc = combine xs (x :: acc)

export
getSplitsLHS : {auto m : Ref MD Metadata} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> Nat -> ClosedTerm -> Name ->
               Core (SplitResult (List ClauseUpdate))
getSplitsLHS fc envlen lhs_in n
    = do let lhs = substLets lhs_in
         logTerm "interaction.casesplit" 3 "Splitting" lhs_in
         let usedns = findAllVars lhs_in

         defs <- get Ctxt

         OK (fn, tyn, cons) <- findCons n lhs
            | SplitFail err => pure (SplitFail err)

         rawlhs <- unelabNoSugar [] lhs
         trycases <- traverse (\c => newLHS fc envlen usedns n c rawlhs) cons

         let Just idx = getNameID fn (gamma defs)
             | Nothing => undefinedName fc fn
         cases <- traverse (mkCase idx rawlhs) trycases

         pure (combine cases [])

export
getSplits : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            (NonEmptyFC -> ClosedTerm -> Bool) -> Name ->
            Core (SplitResult (List ClauseUpdate))
getSplits p n
    = do Just (loc, envlen, lhs_in) <- findLHSAt p
              | Nothing => pure (SplitFail CantFindLHS)
         getSplitsLHS (justFC loc) envlen lhs_in n
