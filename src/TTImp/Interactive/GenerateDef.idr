module TTImp.Interactive.GenerateDef

-- Attempt to generate a complete definition from a type

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.Unify
import Core.Value

import Parser.Lexer.Source

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Interactive.CaseSplit
import TTImp.Interactive.ExprSearch
import TTImp.ProcessDecls
import TTImp.ProcessDef
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

import Data.List

%default covering

fnName : Bool -> Name -> String
fnName lhs (UN n)
    = if isIdentNormal n then n
      else if lhs then "(" ++ n ++ ")"
      else "op"
fnName lhs (NS _ n) = fnName lhs n
fnName lhs (DN s _) = s
fnName lhs n = nameRoot n

-- Make the hole on the RHS have a unique name
uniqueRHS : {auto c : Ref Ctxt Defs} ->
            ImpClause -> Core ImpClause
uniqueRHS (PatClause fc lhs rhs)
    = pure $ PatClause fc lhs !(mkUniqueName rhs)
  where
    mkUniqueName : RawImp -> Core RawImp
    mkUniqueName (IHole fc' rhsn)
        = do defs <- get Ctxt
             rhsn' <- uniqueName defs [] rhsn
             pure (IHole fc' rhsn')
    mkUniqueName tm = pure tm -- it'll be a hole, but this is needed for covering
uniqueRHS c = pure c

expandClause : {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               FC -> SearchOpts -> Int -> ImpClause ->
               Core (Search (List ImpClause))
expandClause loc opts n c
    = do c <- uniqueRHS c
         Right clause <- checkClause linear Private PartialOK False n [] (MkNested []) [] c
            | Left err => noResult -- TODO: impossible clause, do something
                                   -- appropriate

         let MkClause {vars} env lhs rhs = clause
         let Meta _ i fn _ = getFn rhs
            | _ => throw (GenericMsg loc "No searchable hole on RHS")
         defs <- get Ctxt
         Just (Hole locs _) <- lookupDefExact (Resolved fn) (gamma defs)
            | _ => throw (GenericMsg loc "No searchable hole on RHS")
         log "interaction.generate" 10 $ "Expression search for " ++ show (i, fn)
         rhs' <- exprSearchOpts opts loc (Resolved fn) []
         traverse (\rhs' =>
            do let rhsraw = dropLams locs rhs'
               logTermNF "interaction.generate" 5 "Got clause" env lhs
               log "interaction.generate" 5 $ "        = " ++ show rhsraw
               pure [updateRHS c rhsraw]) rhs'
  where
    updateRHS : ImpClause -> RawImp -> ImpClause
    updateRHS (PatClause fc lhs _) rhs = PatClause fc lhs rhs
    -- 'with' won't happen, include for completeness
    updateRHS (WithClause fc lhs wval prf flags cs) rhs
      = WithClause fc lhs wval prf flags cs
    updateRHS (ImpossibleClause fc lhs) _ = ImpossibleClause fc lhs

    dropLams : Nat -> RawImp -> RawImp
    dropLams Z tm = tm
    dropLams (S k) (ILam _ _ _ _ _ sc) = dropLams k sc
    dropLams _ tm = tm

splittableNames : RawImp -> List Name
splittableNames (IApp _ f (IBindVar _ n))
    = splittableNames f ++ [UN n]
splittableNames (IApp _ f _)
    = splittableNames f
splittableNames (IAutoApp _ f _)
    = splittableNames f
splittableNames (INamedApp _ f _ _)
    = splittableNames f
splittableNames _ = []

trySplit : {auto m : Ref MD Metadata} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           FC -> RawImp -> ClosedTerm -> RawImp -> Name ->
           Core (Name, List ImpClause)
trySplit loc lhsraw lhs rhs n
    = do OK updates <- getSplitsLHS loc 0 lhs n
            | _ => pure (n, [])
         pure (n, map (\ups => PatClause loc (updateLHS ups lhsraw) rhs)
                      (mapMaybe valid updates))
  where
    valid : ClauseUpdate -> Maybe (List (Name, RawImp))
    valid (Valid lhs' ups) = Just ups
    valid _ = Nothing

    fixNames : RawImp -> RawImp
    fixNames (IVar loc' (UN n)) = IBindVar loc' n
    fixNames (IVar loc' (MN _ _)) = Implicit loc' True
    fixNames (IApp loc' f a) = IApp loc' (fixNames f) (fixNames a)
    fixNames (IAutoApp loc' f a) = IAutoApp loc' (fixNames f) (fixNames a)
    fixNames (INamedApp loc' f t a) = INamedApp loc' (fixNames f) t (fixNames a)
    fixNames tm = tm

    updateLHS : List (Name, RawImp) -> RawImp -> RawImp
    updateLHS ups (IVar loc' n)
        = case lookup n ups of
               Nothing => IVar loc' n
               Just tm => fixNames tm
    updateLHS ups (IBindVar loc' n)
        = case lookup (UN n) ups of
               Nothing => IBindVar loc' n
               Just tm => fixNames tm
    updateLHS ups (IApp loc' f a) = IApp loc' (updateLHS ups f) (updateLHS ups a)
    updateLHS ups (IAutoApp loc' f a) = IAutoApp loc' (updateLHS ups f) (updateLHS ups a)
    updateLHS ups (INamedApp loc' f t a)
        = INamedApp loc' (updateLHS ups f) t (updateLHS ups a)
    updateLHS ups tm = tm

generateSplits : {auto m : Ref MD Metadata} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 FC -> SearchOpts -> Int -> ImpClause ->
                 Core (List (Name, List ImpClause))
generateSplits loc opts fn (ImpossibleClause fc lhs) = pure []
generateSplits loc opts fn (WithClause fc lhs wval prf flags cs) = pure []
generateSplits loc opts fn (PatClause fc lhs rhs)
    = do (lhstm, _) <-
                elabTerm fn (InLHS linear) [] (MkNested []) []
                         (IBindHere loc PATTERN lhs) Nothing
         let splitnames =
                 if ltor opts then splittableNames lhs
                              else reverse (splittableNames lhs)
         traverse (trySplit fc lhs lhstm rhs) splitnames

collectClauses : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 List (Search (List ImpClause)) ->
                 Core (Search (List ImpClause))
collectClauses [] = one []
collectClauses (x :: xs)
    = do xs' <- collectClauses xs
         combine (++) x xs'

mutual
  tryAllSplits : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 FC -> SearchOpts -> Int ->
                 List (Name, List ImpClause) ->
                 Core (Search (List ImpClause))
  tryAllSplits loc opts n [] = noResult
  tryAllSplits loc opts n ((x, []) :: rest)
      = tryAllSplits loc opts n rest
  tryAllSplits loc opts n ((x, cs) :: rest)
      = do log "interaction.generate" 5 $ "Splitting on " ++ show x
           trySearch (do cs' <- traverse (mkSplits loc opts n) cs
                         collectClauses cs')
                     (tryAllSplits loc opts n rest)

  mkSplits : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> SearchOpts -> Int -> ImpClause ->
             Core (Search (List ImpClause))
  -- If the clause works, use it. Otherwise, split on one of the splittable
  -- variables and try all of the resulting clauses
  mkSplits loc opts n c
      = trySearch
          (if mustSplit opts
              then noResult
              else expandClause loc opts n c)
          (do cs <- generateSplits loc opts n c
              log "interaction.generate" 5 $ "Splits: " ++ show cs
              tryAllSplits loc (record { mustSplit = False,
                                         doneSplit = True } opts) n cs)

export
makeDefFromType : {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  FC ->
                  SearchOpts ->
                  Name -> -- function name to generate
                  Nat -> -- number of arguments
                  ClosedTerm -> -- type of function
                  Core (Search (FC, List ImpClause))
makeDefFromType loc opts n envlen ty
    = tryUnify
         (do defs <- branch
             meta <- get MD
             ust <- get UST
             argns <- getEnvArgNames defs envlen !(nf defs [] ty)
             -- Need to add implicit patterns for the outer environment.
             -- We won't try splitting on these
             let pre_env = replicate envlen (Implicit loc True)

             rhshole <- uniqueName defs [] (fnName False n ++ "_rhs")
             let initcs = PatClause loc
                                (apply (IVar loc n) (pre_env ++ (map (IBindVar loc) argns)))
                                (IHole loc rhshole)
             let Just nidx = getNameID n (gamma defs)
                 | Nothing => undefinedName loc n
             cs' <- mkSplits loc opts nidx initcs
             -- restore the global state, given that we've fiddled with it a lot!
             put Ctxt defs
             put MD meta
             put UST ust
             pure (map (\c => (loc, c)) cs'))
         noResult

export
makeDef : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          (NonEmptyFC -> (Name, Nat, ClosedTerm) -> Bool) ->
          Name -> Core (Search (FC, List ImpClause))
makeDef p n
    = do Just (loc, nidx, envlen, ty) <- findTyDeclAt p
            | Nothing => noResult
         n <- getFullName nidx
         logTerm "interaction.generate" 5 ("Searching for " ++ show n) ty
         let opts = record { genExpr = Just (makeDefFromType (justFC loc)) }
                           (initSearchOpts True 5)
         makeDefFromType (justFC loc) opts n envlen ty

-- Given a clause, return the bindable names, and the ones that were used in
-- the rhs
bindableUsed : ImpClause -> Maybe (List Name, List Name)
bindableUsed (PatClause fc lhs rhs)
    = let lhsns = findIBindVars lhs
          rhsns = findAllNames [] rhs in
          Just (lhsns, filter (\x => x `elem` lhsns) rhsns)
bindableUsed _ = Nothing

propBindableUsed : List ImpClause -> Double
propBindableUsed def
    = let (b, u) = getProp def in
          if b == Z
             then 1.0
             else the Double (cast u) / the Double (cast b)
  where
    getProp : List ImpClause -> (Nat, Nat)
    getProp [] = (0, 0)
    getProp (c :: xs)
        = let (b, u) = getProp xs in
              case bindableUsed c of
                   Nothing => (b, u)
                   Just (b', u') => (b + length (nub b'), u + length (nub u'))

-- Sort by highest proportion of bound variables used. This recalculates every
-- time it looks, which might seem expensive, but it's only inspecting (not
-- constructing anything) and it would make the code ugly if we avoid that.
-- Let's see if it's a bottleneck before doing anything about it...
export
mostUsed : List ImpClause -> List ImpClause -> Ordering
mostUsed def1 def2 = compare (propBindableUsed def2) (propBindableUsed def1)

export
makeDefSort : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              (NonEmptyFC -> (Name, Nat, ClosedTerm) -> Bool) ->
              Nat -> (List ImpClause -> List ImpClause -> Ordering) ->
              Name -> Core (Search (FC, List ImpClause))
makeDefSort p max ord n
    = searchSort max (makeDef p n) (\x, y => ord (snd x) (snd y))

export
makeDefN : {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           (NonEmptyFC -> (Name, Nat, ClosedTerm) -> Bool) ->
           Nat -> Name -> Core (List (FC, List ImpClause))
makeDefN p max n
    = do (res, _) <- searchN max (makeDef p n)
         pure res
