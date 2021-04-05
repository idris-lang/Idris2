module TTImp.Interactive.ExprSearch

-- Expression search for interactive editing. There's a lot of similarities
-- with Core.AutoSearch (and we reuse some of it) but I think it's better for
-- them to be entirely separate: AutoSearch is a crucial part of the core
-- therefore it's good for it to be well defined and cleanly separated from
-- everything else, whereas this search mechanism is about finding plausible
-- candidates for programs.

-- We try to find as many results as possible, within the given search
-- depth.

import Core.AutoSearch
import Core.CaseTree
import Core.Context
import Core.Context.Log
import Core.Env
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Interactive.CaseSplit
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

import Libraries.Data.Bool.Extra
import Data.Either
import Data.List

%default covering

-- Data for building recursive calls - the function name, and the structure
-- of the LHS. Only recursive calls with a different structure are okay.
record RecData where
  constructor MkRecData
  {vars : List Name}
  recname : Name -- resolved name
  lhsapp : Term vars

-- Additional definitions required to support the result
ExprDefs : Type
ExprDefs = List ImpDecl

export
data Search : Type -> Type where
     NoMore : Search a -- no more results
     Result : a -> Core (Search a) -> Search a
       -- ^ a result, and what to do if the result is considered
       -- unacceptable

export
Functor Search where
  map fn NoMore = NoMore
  map fn (Result res next)
      = Result (fn res)
               (do next' <- next
                   pure (map fn next'))

export
one : a -> Core (Search a)
one res = pure $ Result res (pure NoMore)

export
noResult : Core (Search a)
noResult = pure NoMore

export
traverse : (a -> Core b) -> Search a -> Core (Search b)
traverse f NoMore = pure NoMore
traverse f (Result r next)
    = do r' <- f r
         pure (Result r' (do next' <- next
                             traverse f next'))

export
filterS : (a -> Bool) -> Search a -> Core (Search a)
filterS p NoMore = pure NoMore
filterS p (Result r next)
    = do next' <- next
         let fnext = filterS p next'
         if p r
            then pure $ Result r fnext
            else fnext

export
searchN : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          Nat -> Core (Search a) -> Core (List a, Core (Search a))
searchN max s
    = tryUnify
         (do res <- s
             xs <- count max res
             pure xs)
         (pure ([], pure NoMore))
  where
    count : Nat -> Search a -> Core (List a, Core (Search a))
    count k NoMore = pure ([], pure NoMore)
    count Z _ = pure ([], pure NoMore)
    count (S Z) (Result a next) = pure ([a], next)
    count (S k) (Result a next)
        = do (rest, cont) <- count k !next
             pure $ (a :: rest, cont)

-- Generate definitions in batches, and sort according to some user provided
-- heuristic (highest proportion of bound variables used is a good one!)
export
searchSort : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Nat -> Core (Search a) ->
             (a -> a -> Ordering) ->
             Core (Search a)
searchSort max s ord
    = do (batch, next) <- searchN max s
         if isNil batch
            then pure NoMore
            else returnBatch (sortBy ord batch) next
  where
    returnBatch : List a -> Core (Search a) -> Core (Search a)
    returnBatch [] res = searchSort max res ord
    returnBatch (res :: xs) x
        = pure (Result res (returnBatch xs x))

export
nextResult : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Core (Search a) -> Core (Maybe (a, Core (Search a)))
nextResult s
    = tryUnify
         (do res <- s
             case res of
                  NoMore => pure Nothing
                  Result r next => pure (Just (r, next)))
         (pure Nothing)

public export
record SearchOpts where
  constructor MkSearchOpts
  holesOK : Bool -- add a hole on getting stuck, rather than an error
  getRecData : Bool -- update the LHS data
  recData : Maybe RecData -- LHS, to help build recursive calls
  depth : Nat -- maximum search depth
  inArg : Bool -- in an argument (not top level). Here, try recursive calls
               -- before constructors, otherwise try recursive calls last
  inUnwrap : Bool
  ltor : Bool -- case split left to right
              -- (right to left is good for auxiliary definitions, because
              -- then we split on the new pattern first)
  mustSplit : Bool -- must begin with a case split (in a case helper)
  doneSplit : Bool -- definitely under a case split
  genExpr : Maybe (SearchOpts -> Name -> Nat -> ClosedTerm ->
                   Core (Search (FC, List ImpClause)))

export
initSearchOpts : (rec : Bool) -> (maxDepth : Nat) -> SearchOpts
initSearchOpts rec depth
    = MkSearchOpts False rec Nothing depth
                   False False True False False
                   Nothing

search : {auto c : Ref Ctxt Defs} ->
         {auto m : Ref MD Metadata} ->
         {auto u : Ref UST UState} ->
         FC -> RigCount ->
         SearchOpts -> ClosedTerm ->
         Name -> Core (Search (ClosedTerm, ExprDefs))

getAllEnv : {vars : _} -> FC ->
            SizeOf done ->
            Env Term vars ->
            List (Term (done ++ vars), Term (done ++ vars))
getAllEnv fc done [] = []
getAllEnv {vars = v :: vs} {done} fc p (b :: env)
   = let rest = getAllEnv fc (sucR p) env
         MkVar var = weakenVar p (MkVar First)
         usable = usableName v in
         if usable
            then (Local fc Nothing _ var,
                     rewrite appendAssociative done [v] vs in
                        weakenNs (sucR p) (binderType b)) ::
                             rewrite appendAssociative done [v] vs in rest
            else rewrite appendAssociative done [v] vs in rest
  where
    usableName : Name -> Bool
    usableName (UN _) = True
    usableName _ = False

-- Search recursively, but only if the given name wasn't solved by unification
searchIfHole : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               FC -> SearchOpts -> ClosedTerm ->
               Env Term vars -> ArgInfo vars ->
               Core (Search (Term vars, ExprDefs))
searchIfHole fc opts topty env arg
    = case depth opts of
           Z => noResult
           S k =>
              do let hole = holeID arg
                 let rig = argRig arg
                 defs <- get Ctxt
                 Just gdef <- lookupCtxtExact (Resolved hole) (gamma defs)
                      | Nothing => noResult
                 let Hole _ _ = definition gdef
                      | _ => one (!(normaliseHoles defs env (metaApp arg)), [])
                                -- already solved
                 res <- search fc rig (record { depth = k,
                                                inArg = True } opts)
                               topty (Resolved hole)
                 -- When we solve an argument, we're also building a lambda
                 -- expression for its environment, so we need to apply it to
                 -- the current environment to use it as an argument.
                 traverse (\(tm, ds) =>
                    pure (!(normaliseHoles defs env
                             (applyTo fc (embed tm) env)), ds)) res

explicit : ArgInfo vars -> Bool
explicit ai
    = case plicit ai of
           Explicit => True
           _ => False

firstSuccess : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               List (Core (Search a)) ->
               Core (Search a)
firstSuccess [] = noResult
firstSuccess (elab :: elabs)
    = do ust <- get UST
         defs <- get Ctxt
         catch (do Result res more <- elab
                      | NoMore => continue ust defs elabs
                   pure (Result res (continue ust defs (more :: elabs))))
               (\err => continue ust defs elabs)
  where
    continue : UState -> Defs -> List (Core (Search a)) ->
               Core (Search a)
    continue ust defs elabs
        = do put UST ust
             put Ctxt defs
             firstSuccess elabs

-- Take the first successful result of the two given searches
export
trySearch : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Core (Search a) ->
            Core (Search a) ->
            Core (Search a)
trySearch s1 s2 = firstSuccess [s1, s2]

export
combine : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          (a -> b -> t) -> Search a -> Search b -> Core (Search t)
combine f NoMore y = pure NoMore
combine f (Result x next) NoMore = pure NoMore
combine f (Result x nextx) (Result y nexty)
    = pure $ Result (f x y) $
                     (do nexty' <- nexty
                         combine f !(one x) nexty')
                         `trySearch`
                     ((do nextx' <- nextx
                          combine f nextx' !(one y))
                          `trySearch`
                      (do nextx' <- nextx
                          nexty' <- nexty
                          combine f nextx' nexty'))

mkCandidates : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               FC -> Term vars -> ExprDefs ->
               List (Search (Term vars, ExprDefs)) ->
               Core (Search (Term vars, ExprDefs))
-- out of arguments, we have a candidate
mkCandidates fc f ds [] = one (f, ds)
-- argument has run out of ideas, we're stuck
mkCandidates fc f ds (NoMore :: argss) = noResult
-- make a candidate from 'f arg' applied to the rest of the arguments
mkCandidates fc f ds (Result (arg, ds') next :: argss)
    = firstSuccess
           [mkCandidates fc (App fc f arg) (ds ++ ds') argss,
            do next' <- next
               mkCandidates fc f ds (next' :: argss)]

-- Apply the name to arguments and see if the result unifies with the target
-- type, then try to automatically solve any holes which were generated.
-- If there are any remaining holes, search fails.
searchName : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount -> SearchOpts ->
             Env Term vars -> NF vars -> ClosedTerm ->
             (Name, GlobalDef) ->
             Core (Search (Term vars, ExprDefs))
searchName fc rigc opts env target topty (n, ndef)
    = do defs <- get Ctxt
         let True = visibleInAny (!getNS :: !getNestedNS)
                                 (fullname ndef) (visibility ndef)
             | _ => noResult
         let ty = type ndef
         let True = usableName (fullname ndef)
             | _ => noResult
         let namety : NameType
                 = case definition ndef of
                        DCon tag arity _ => DataCon tag arity
                        TCon tag arity _ _ _ _ _ _ => TyCon tag arity
                        _ => Func
         log "interaction.search" 5 $ "Trying " ++ show (fullname ndef)
         nty <- nf defs env (embed ty)
         (args, appTy) <- mkArgs fc rigc env nty
         logNF "interaction.search" 5 "Target" env target
         logNF "interaction.search" 10 "App type" env appTy
         ures <- unify inSearch fc env target appTy
         let [] = constraints ures
             | _ => noResult
         -- Search the explicit arguments first, they may resolve other holes
         traverse_ (searchIfHole fc opts topty env)
                   (filter explicit args)
         args' <- traverse (searchIfHole fc opts topty env)
                           args
         mkCandidates fc (Ref fc namety n) [] args'
  where
    -- we can only use the name in a search result if it's a user writable
    -- name (so, no recursive with blocks or case blocks, for example)
    usableName : Name -> Bool
    usableName (UN _) = True
    usableName (NS _ n) = usableName n
    usableName (Nested _ n) = usableName n
    usableName _ = False

getSuccessful : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                FC -> RigCount -> SearchOpts -> Bool ->
                Env Term vars -> Term vars -> ClosedTerm ->
                List (Core (Search (Term vars, ExprDefs))) ->
                Core (Search (Term vars, ExprDefs))
getSuccessful {vars} fc rig opts mkHole env ty topty all
    = do res <- firstSuccess all
         case res of
              NoMore => -- If no successful search, make a hole
                if mkHole && holesOK opts
                   then do defs <- get Ctxt
                           let base = maybe "arg"
                                            (\r => nameRoot (recname r) ++ "_rhs")
                                            (recData opts)
                           hn <- uniqueName defs (map nameRoot vars) base
                           (idx, tm) <- newMeta fc rig env (UN hn) ty
                                                (Hole (length env) (holeInit False))
                                                False
                           one (tm, [])
                   else noResult
              r => pure r

searchNames : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount -> SearchOpts -> Env Term vars ->
              Term vars -> ClosedTerm ->
              List Name -> Core (Search (Term vars, ExprDefs))
searchNames fc rig opts env ty topty []
    = noResult
searchNames fc rig opts env ty topty (n :: ns)
    = do defs <- get Ctxt
         vis <- traverse (visible (gamma defs) (currentNS defs :: nestedNS defs)) (n :: ns)
         let visns = mapMaybe id vis
         nfty <- nf defs env ty
         logTerm "interaction.search" 10 ("Searching " ++ show (map fst visns) ++ " for ") ty
         getSuccessful fc rig opts False env ty topty
            (map (searchName fc rig opts env nfty topty) visns)
  where
    visible : Context -> List Namespace -> Name ->
              Core (Maybe (Name, GlobalDef))
    visible gam nspace n
        = do Just def <- lookupCtxtExact n gam
                  | Nothing => pure Nothing
             if visibleInAny nspace n (visibility def)
                then pure (Just (n, def))
                else pure Nothing

tryRecursive : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               FC -> RigCount -> SearchOpts ->
               Env Term vars -> Term vars -> ClosedTerm ->
               RecData -> Core (Search (Term vars, ExprDefs))
tryRecursive fc rig opts env ty topty rdata
    = do defs <- get Ctxt
         case !(lookupCtxtExact (recname rdata) (gamma defs)) of
              Nothing => noResult
              Just def =>
                do res <- searchName fc rig (record { recData = Nothing } opts)
                                     env !(nf defs env ty)
                                     topty (recname rdata, def)
                   defs <- get Ctxt
                   res' <- traverse (\ (t, ds) => pure (!(toFullNames t), ds)) res
                   filterS (structDiffTm (lhsapp rdata)) res'
  where
    mutual
      -- A fairly simple superficialy syntactic check to make sure that
      -- the recursive call is structurally different from the lhs
      -- (Essentially, meaning that there's a constructor application in
      -- one where there's a local in another, or that constructor applications
      -- differ somewhere)
      argDiff : Term vs -> Term vs' -> Bool
      argDiff (Local _ _ _ _) _ = False
      argDiff (Ref _ _ fn) (Ref _ _ fn') = fn /= fn'
      argDiff (Bind _ _ _ _) _ = False
      argDiff _ (Bind _ _ _ _) = False
      argDiff (App _ f a) (App _ f' a')
         = structDiff f f' || structDiff a a'
      argDiff (PrimVal _ c) (PrimVal _ c') = c /= c'
      argDiff (Erased _ _) _ = False
      argDiff _ (Erased _ _) = False
      argDiff (TType _) (TType _) = False
      argDiff (As _ _ _ x) y = argDiff x y
      argDiff x (As _ _ _ y) = argDiff x y
      argDiff _ _ = True

      appsDiff : Term vs -> Term vs' -> List (Term vs) -> List (Term vs') ->
                 Bool
      appsDiff (Ref _ (DataCon _ _) f) (Ref _ (DataCon _ _) f') args args'
         = f /= f' || anyTrue (zipWith argDiff args args')
      appsDiff (Ref _ (TyCon _ _) f) (Ref _ (TyCon _ _) f') args args'
         = f /= f' || anyTrue (zipWith argDiff args args')
      appsDiff (Ref _ _ f) (Ref _ _ f') args args'
         = f == f'
           && length args == length args'
           && anyTrue (zipWith argDiff args args')
      appsDiff (Ref _ (DataCon _ _) f) (Local _ _ _ _) _ _ = True
      appsDiff (Local _ _ _ _) (Ref _ (DataCon _ _) f) _ _ = True
      appsDiff f f' [] [] = argDiff f f'
      appsDiff _ _ _ _ = False -- can't be sure...

      -- Reject if the recursive call is the same in structure as the lhs
      structDiff : Term vs -> Term vs' -> Bool
      structDiff tm tm'
         = let (f, args) = getFnArgs tm
               (f', args') = getFnArgs tm' in
               appsDiff f f' args args'

      structDiffTm : Term vs -> (Term vs', ExprDefs) -> Bool
      structDiffTm tm (tm', _) = structDiff tm tm'

-- A local is usable as long as its type isn't a hole
usableLocal : FC -> Env Term vars -> NF vars -> Bool
usableLocal loc env (NApp _ (NMeta _ _ _) args) = False
usableLocal loc _ _ = True

searchLocalWith : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  FC -> Bool ->
                  RigCount -> SearchOpts -> Env Term vars ->
                  List (Term vars, Term vars) ->
                  Term vars -> ClosedTerm ->
                  Core (Search (Term vars, ExprDefs))
searchLocalWith fc nofn rig opts env [] ty topty
    = noResult
searchLocalWith {vars} fc nofn rig opts env ((p, pty) :: rest) ty topty
    = do defs <- get Ctxt
         nty <- nf defs env ty
         getSuccessful fc rig opts False env ty topty
                       [findPos defs p id !(nf defs env pty) nty,
                        searchLocalWith fc nofn rig opts env rest ty
                                        topty]
  where
    findDirect : Defs -> Term vars ->
                 (Term vars -> Term vars) ->
                 NF vars -> -- local variable's type
                 NF vars -> -- type we're looking for
                 Core (Search (Term vars, ExprDefs))
    findDirect defs prf f nty ty
        = do (args, appTy) <- mkArgs fc rig env nty
             -- We can only use a local variable if it's not an unsolved
             -- hole
             if usableLocal fc env nty
                then
                  tryUnify -- try with no arguments first
                    (do when (not (isNil args) && nofn) $
                             throw (InternalError "Must apply function")
                        ures <- unify inTerm fc env ty nty
                        let [] = constraints ures
                            | _ => throw (InternalError "Can't use directly")
                        mkCandidates fc (f prf) [] [])
                    (do ures <- unify inTerm fc env ty appTy
                        let [] = constraints ures
                            | _ => noResult
                        args' <- traverse (searchIfHole fc opts topty env)
                                          args
                        mkCandidates fc (f prf) [] args')
                else noResult

    findPos : Defs -> Term vars ->
              (Term vars -> Term vars) ->
              NF vars -> NF vars -> Core (Search (Term vars, ExprDefs))
    findPos defs prf f x@(NTCon pfc pn _ _ [(fc1, xty), (fc2, yty)]) target
        = getSuccessful fc rig opts False env ty topty
              [findDirect defs prf f x target,
                 (do fname <- maybe (throw (InternalError "No fst"))
                                    pure
                                    !fstName
                     sname <- maybe (throw (InternalError "No snd"))
                                    pure
                                    !sndName
                     if !(isPairType pn)
                        then do empty <- clearDefs defs
                                xtytm <- quote empty env xty
                                ytytm <- quote empty env yty
                                getSuccessful fc rig opts False env ty topty
                                  [(do xtynf <- evalClosure defs xty
                                       findPos defs prf
                                         (\arg => applyWithFC (Ref fc Func fname)
                                                          [(fc1, xtytm),
                                                           (fc2, ytytm),
                                                           (fc, f arg)])
                                         xtynf target),
                                   (do ytynf <- evalClosure defs yty
                                       findPos defs prf
                                           (\arg => applyWithFC (Ref fc Func sname)
                                                          [(fc1, xtytm),
                                                           (fc2, ytytm),
                                                           (fc, f arg)])
                                           ytynf target)]
                         else noResult)]
    findPos defs prf f nty target = findDirect defs prf f nty target

searchLocal : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              FC -> RigCount -> SearchOpts ->
              Env Term vars -> Term vars -> ClosedTerm ->
              Core (Search (Term vars, ExprDefs))
searchLocal fc rig opts env ty topty
    = -- Reverse the environment so we try the patterns left to right.
      -- This heuristic is just so arguments appear the same order in
      -- recursive calls
      searchLocalWith fc False rig opts env (reverse (getAllEnv fc zero env))
                      ty topty

makeHelper : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount -> SearchOpts ->
             Env Term vars ->
             Term vars -> Term vars -> Search (Term vars, ExprDefs) ->
             Core (Search (Term vars, ExprDefs))
makeHelper fc rig opts env letty targetty NoMore
    = pure NoMore
makeHelper fc rig opts env letty targetty (Result (locapp, ds) next)
    = do let S depth' = depth opts
             | Z => noResult
         logTerm "interaction.search" 10 "Local app" locapp
         let Just gendef = genExpr opts
             | Nothing => noResult
         defs <- get Ctxt
         intn <- genVarName "cval"
         helpern_in <- genCaseName "search"
         helpern <- inCurrentNS helpern_in
         let env' = Lam fc top Explicit letty :: env
         scopeMeta <- metaVar fc top env' helpern
                             (weaken {n = intn} targetty)
         let scope = toApp scopeMeta
         updateDef helpern (const (Just None))
         -- Apply the intermediate result to the helper function we're
         -- about to generate.
         let def = App fc (Bind fc intn (Lam fc top Explicit letty) scope)
                          locapp

         logTermNF "interaction.search" 10 "Binding def" env def
         defs <- get Ctxt
         Just ty <- lookupTyExact helpern (gamma defs)
             | Nothing => throw (InternalError "Can't happen")
         logTermNF "interaction.search" 10 "Type of scope name" [] ty

         -- Generate a definition for the helper, but with more restrictions.
         -- Always take the first result, to avoid blowing up search space.
         -- Go right to left on variable split, to get the variable we just
         -- added first.
         -- There must be at least one case split.
         ((helper :: _), nextdef) <-
                    searchN 1 $ gendef (record { getRecData = False,
                                                 inUnwrap = True,
                                                 depth = depth',
                                                 ltor = False,
                                                 mustSplit = True } opts)
                                       helpern 0 ty
              | _ => do log "interaction.search" 10 "No results"
                        noResult

         let helperdef = IDef fc helpern (snd helper)
         log "interaction.search" 10 $ "Def: " ++ show helperdef
         pure (Result (def, helperdef :: ds) -- plus helper
                      (do next' <- next
                          makeHelper fc rig opts env letty targetty next'))
  where
    -- convert a metavar application (as created by 'metaVar') to a normal
    -- application (as required by a case block)
    toApp : forall vars . Term vars -> Term vars
    toApp (Meta fc n i args) = apply fc (Ref fc Func (Resolved i)) args
    toApp tm = tm


tryIntermediateWith : {vars : _} ->
                      {auto c : Ref Ctxt Defs} ->
                      {auto m : Ref MD Metadata} ->
                      {auto u : Ref UST UState} ->
                      FC -> RigCount -> SearchOpts ->
                      Env Term vars -> List (Term vars, Term vars) ->
                      Term vars -> ClosedTerm ->
                      Core (Search (Term vars, ExprDefs))
tryIntermediateWith fc rig opts env [] ty topty = noResult
tryIntermediateWith fc rig opts env ((p, pty) :: rest) ty topty
    = do defs <- get Ctxt
         getSuccessful fc rig opts False env ty topty
                       [applyLocal defs p !(nf defs env pty) ty,
                        tryIntermediateWith fc rig opts env rest ty
                                            topty]
  where
    matchable : Defs -> NF vars -> Core Bool
    matchable defs (NBind fc x (Pi _ _ _ _) sc)
        = matchable defs !(sc defs (toClosure defaultOpts env
                                              (Erased fc False)))
    matchable defs (NTCon _ _ _ _ _) = pure True
    matchable _ _ = pure False

    applyLocal : Defs -> Term vars ->
                 NF vars -> Term vars -> Core (Search (Term vars, ExprDefs))
    applyLocal defs tm locty@(NBind _ x (Pi fc' _ _ _) sc) targetty
        = -- If the local has a function type, and the return type is
          -- something we can pattern match on (so, NTCon) then apply it,
          -- let bind the result, and try to generate a definition for
          -- the scope of the let binding
          do True <- matchable defs
                           !(sc defs (toClosure defaultOpts env
                                                (Erased fc False)))
                 | False => noResult
             intnty <- genVarName "cty"
             letty <- metaVar fc' erased env intnty (TType fc)
             let opts' = record { inUnwrap = True } opts
             locsearch <- searchLocalWith fc True rig opts' env [(p, pty)]
                                          letty topty
             makeHelper fc rig opts env letty targetty locsearch
    applyLocal defs tm _ _ = noResult

-- Try to make progress by applying a local variable or the recursive
-- definition to an argument, then making a helper function to complete
-- the job
tryIntermediate : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  FC -> RigCount -> SearchOpts ->
                  Env Term vars -> Term vars -> ClosedTerm ->
                  Core (Search (Term vars, ExprDefs))
tryIntermediate fc rig opts env ty topty
    = tryIntermediateWith fc rig opts env (reverse (getAllEnv fc zero env))
                          ty topty

-- Try making a recursive call and unpacking the result. Only do this if
-- the return type is a single constructor data type, otherwise it massively
-- increases the search space, and the intention is for unpacking
-- things like dependent pairs and singleton types before proceeding.
tryIntermediateRec : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto m : Ref MD Metadata} ->
                     {auto u : Ref UST UState} ->
                     FC -> RigCount -> SearchOpts ->
                     Env Term vars ->
                     Term vars -> ClosedTerm ->
                     Maybe RecData -> Core (Search (Term vars, ExprDefs))
tryIntermediateRec fc rig opts env ty topty Nothing = noResult
tryIntermediateRec fc rig opts env ty topty (Just rd)
    = do defs <- get Ctxt
         Just rty <- lookupTyExact (recname rd) (gamma defs)
              | Nothing => noResult
         True <- isSingleCon defs !(nf defs [] rty)
              | _ => noResult
         intnty <- genVarName "cty"
         letty <- metaVar fc erased env intnty (TType fc)
         let opts' = record { inUnwrap = True,
                              recData = Nothing } opts
         logTerm "interaction.search" 10 "Trying recursive search for" ty
         log "interaction.search" 10 $ show !(toFullNames (recname rd))
         logTerm "interaction.search" 10 "LHS" !(toFullNames (lhsapp rd))
         recsearch <- tryRecursive fc rig opts' env letty topty rd
         makeHelper fc rig opts' env letty ty recsearch
  where
    isSingleCon : Defs -> NF [] -> Core Bool
    isSingleCon defs (NBind fc x (Pi _ _ _ _) sc)
        = isSingleCon defs !(sc defs (toClosure defaultOpts []
                                              (Erased fc False)))
    isSingleCon defs (NTCon _ n _ _ _)
        = do Just (TCon _ _ _ _ _ _ [con] _) <- lookupDefExact n (gamma defs)
                  | _ => pure False
             pure True
    isSingleCon _ _ = pure False

searchType : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount -> SearchOpts -> Env Term vars ->
             ClosedTerm ->
             Nat -> Term vars -> Core (Search (Term vars, ExprDefs))
searchType fc rig opts env topty (S k) (Bind bfc n b@(Pi fc' c info ty) sc)
    = do let env' : Env Term (n :: _) = b :: env
         log "interaction.search" 10 $ "Introduced lambda, search for " ++ show sc
         scVal <- searchType fc rig opts env' topty k sc
         pure (map (\ (sc, ds) => (Bind bfc n (Lam fc' c info ty) sc, ds)) scVal)
searchType {vars} fc rig opts env topty Z (Bind bfc n b@(Pi fc' c info ty) sc)
    = -- try a local before creating a lambda...
      getSuccessful fc rig opts False env ty topty
           [searchLocal fc rig opts env (Bind bfc n b sc) topty,
            (do defs <- get Ctxt
                let n' = UN !(getArgName defs n [] vars !(nf defs env ty))
                let env' : Env Term (n' :: _) = b :: env
                let sc' = renameTop n' sc
                log "interaction.search" 10 $ "Introduced lambda, search for " ++ show sc'
                scVal <- searchType fc rig opts env' topty Z sc'
                pure (map (\ (sc, ds) =>
                             (Bind bfc n' (Lam fc' c info ty) sc, ds)) scVal))]
searchType fc rig opts env topty _ ty
    = case getFnArgs ty of
           (Ref rfc (TyCon t ar) n, args) =>
                do defs <- get Ctxt
                   if length args == ar
                     then do sd <- getSearchData fc False n
                             let allHints = concat (map snd (hintGroups sd))
                             -- Solutions is either:
                             -- First try the locals,
                             -- Then try the hints in order
                             -- Then try a recursive call
                             log "interaction.search" 10 $ "Hints found for " ++ show n ++ " "
                                         ++ show allHints
                             let tries =
                                   [searchLocal fc rig opts env ty topty,
                                    searchNames fc rig opts env ty topty allHints]
                             let tryRec =
                                   case recData opts of
                                        Nothing => []
                                        Just rd => [tryRecursive fc rig opts env ty topty rd]
                             let tryIntRec =
                                   if doneSplit opts
                                      then [tryIntermediateRec fc rig opts env ty topty (recData opts)]
                                      else []
                             let tryInt = if not (inUnwrap opts)
                                             then [tryIntermediate fc rig opts env ty topty]
                                             else []
                             -- if we're in an argument, try the recursive call
                             -- first. We're more likely to want that than nested
                             -- constructors.
                             let allns : List _
                                     = if inArg opts
                                          then tryRec ++ tryInt ++ tries
                                          else tryInt ++ tries ++ tryRec ++ tryIntRec
                             getSuccessful fc rig opts True env ty topty allns
                     else noResult
           _ => do logTerm "interaction.search" 10 "Searching locals only at" ty
                   let tryInt = if not (inUnwrap opts)
                                   then [tryIntermediate fc rig opts env ty topty]
                                   else []
                   let tryIntRec = if inArg opts || not (doneSplit opts)
                                      then []
                                      else [tryIntermediateRec fc rig opts env ty topty (recData opts)]
                   getSuccessful fc rig opts True env ty topty
                           (tryInt ++ [searchLocal fc rig opts env ty topty]
                             ++ case recData opts of
                                     Nothing => []
                                     Just rd => [tryRecursive fc rig opts env ty topty rd]
                             ++ tryIntRec)

searchHole : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> RigCount -> SearchOpts -> Name ->
             Nat -> ClosedTerm ->
             Defs -> GlobalDef -> Core (Search (ClosedTerm, ExprDefs))
searchHole fc rig opts n locs topty defs glob
    = do searchty <- normalise defs [] (type glob)
         logTerm "interaction.search" 10 "Normalised type" searchty
         searchType fc rig opts [] topty locs searchty

-- Declared at the top
search fc rig opts topty n_in
    = do defs <- get Ctxt
         case !(lookupHoleName n_in (gamma defs)) of
              Just (n, i, gdef) =>
                   -- The definition should be 'BySearch' at this stage,
                   -- if it's arising from an auto implicit
                   case definition gdef of
                        Hole locs _ => searchHole fc rig opts n locs topty defs gdef
                        BySearch _ _ _ => searchHole fc rig opts n
                                                   !(getArity defs [] (type gdef))
                                                   topty defs gdef
                        _ => do log "interaction.search" 10 $ show n_in ++ " not a hole"
                                throw (InternalError $ "Not a hole: " ++ show n ++ " in " ++
                                        show (map recname (recData opts)))
              _ => do log "interaction.search" 10 $ show n_in ++ " not found"
                      undefinedName fc n_in
  where
    lookupHoleName : Name -> Context ->
                     Core (Maybe (Name, Int, GlobalDef))
    lookupHoleName n defs
        = case !(lookupCtxtExactI n defs) of
               Just (i, res) => pure $ Just (n, i, res)
               Nothing => case !(lookupCtxtName n defs) of
                               [res] => pure $ Just res
                               _ => pure Nothing

getLHSData : {auto c : Ref Ctxt Defs} ->
             Defs -> Maybe ClosedTerm -> Core (Maybe RecData)
getLHSData defs Nothing = pure Nothing
getLHSData defs (Just tm)
    = pure $ getLHS !(toFullNames !(normaliseHoles defs [] tm))
  where
    getLHS : {vars : _} -> Term vars -> Maybe RecData
    getLHS (Bind _ _ (PVar _ _ _ _) sc) = getLHS sc
    getLHS (Bind _ _ (PLet _ _ _ _) sc) = getLHS sc
    getLHS sc
        = case getFn sc of
               Ref _ _ n => Just (MkRecData n sc)
               _ => Nothing

firstLinearOK : {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                FC -> Search (ClosedTerm, ExprDefs) ->
                Core (Search RawImp)
firstLinearOK fc NoMore = noResult
firstLinearOK fc (Result (t, ds) next)
    = handleUnify
            (do unless (isNil ds) $
                   traverse_ (processDecl [InCase] (MkNested []) []) ds
                ignore $ linearCheck fc linear False [] t
                defs <- get Ctxt
                nft <- normaliseHoles defs [] t
                raw <- unelab [] !(toFullNames nft)
                pure (Result raw (firstLinearOK fc !next)))
            (\err =>
                do next' <- next
                   firstLinearOK fc next')

export
exprSearchOpts : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 SearchOpts -> FC -> Name -> List Name ->
                 Core (Search RawImp)
exprSearchOpts opts fc n_in hints
    = do defs <- get Ctxt
         Just (n, idx, gdef) <- lookupHoleName n_in defs
             | Nothing => undefinedName fc n_in
         lhs <- findHoleLHS !(getFullName (Resolved idx))
         log "interaction.search" 10 $ "LHS hole data " ++ show (n, lhs)
         opts' <- if getRecData opts
                     then do d <- getLHSData defs lhs
                             pure (record { recData = d } opts)
                     else pure opts
         res <- search fc (multiplicity gdef) opts' (type gdef) n
         firstLinearOK fc res
  where
    lookupHoleName : Name -> Defs -> Core (Maybe (Name, Int, GlobalDef))
    lookupHoleName n defs
        = case !(lookupCtxtExactI n (gamma defs)) of
               Just (idx, res) => pure $ Just (n, idx, res)
               Nothing => case !(lookupCtxtName n (gamma defs)) of
                               [res] => pure $ Just res
                               _ => pure Nothing

export
exprSearch : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> Name -> List Name ->
             Core (Search RawImp)
exprSearch = exprSearchOpts (initSearchOpts True 5)

export
exprSearchN : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              FC -> Nat -> Name -> List Name ->
              Core (List RawImp)
exprSearchN fc max n hints
    = do (res, _) <- searchN max (exprSearch fc n hints)
         pure res
