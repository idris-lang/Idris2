module TTImp.Interactive.GenerateDef

-- Attempt to generate a complete definition from a type

import Core.Context
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
               FC -> Int -> ImpClause ->
               Core (List ImpClause)
expandClause loc n c
    = do log 10 $ "Trying clause " ++ show c
         c <- uniqueRHS c
         Right clause <- checkClause linear False n [] (MkNested []) [] c
            | Left _ => pure [] -- TODO: impossible clause, do something
                                -- appropriate
         let MkClause {vars} env lhs rhs = clause
         logTerm 10 "RHS hole" rhs
         let Meta _ i fn _ = getFn rhs
            | _ => throw (GenericMsg loc "No searchable hole on RHS")
         defs <- get Ctxt
         Just (Hole locs _) <- lookupDefExact (Resolved fn) (gamma defs)
            | _ => throw (GenericMsg loc "No searchable hole on RHS")
         log 10 $ "Expression search for " ++ show (i, fn)
         (rhs' :: _) <- exprSearch loc (Resolved fn) []
            | _ => throw (GenericMsg loc "No result found for search on RHS")
         defs <- get Ctxt
         rhsnf <- normaliseHoles defs [] rhs'
         let (_ ** (env', rhsenv)) = dropLams locs [] rhsnf

         rhsraw <- unelab env' rhsenv
         logTermNF 5 "Got clause" env lhs
         logTermNF 5 "        = " env' rhsenv
         pure [updateRHS c rhsraw]
  where
    updateRHS : ImpClause -> RawImp -> ImpClause
    updateRHS (PatClause fc lhs _) rhs = PatClause fc lhs rhs
    -- 'with' won't happen, include for completeness
    updateRHS (WithClause fc lhs wval flags cs) rhs = WithClause fc lhs wval flags cs
    updateRHS (ImpossibleClause fc lhs) _ = ImpossibleClause fc lhs

    dropLams : {vars : _} ->
               Nat -> Env Term vars -> Term vars ->
               (vars' ** (Env Term vars', Term vars'))
    dropLams Z env tm = (_ ** (env, tm))
    dropLams (S k) env (Bind _ _ b sc) = dropLams k (b :: env) sc
    dropLams _ env tm = (_ ** (env, tm))

splittableNames : RawImp -> List Name
splittableNames (IApp _ f (IBindVar _ n))
    = splittableNames f ++ [UN n]
splittableNames (IApp _ f _)
    = splittableNames f
splittableNames (IImplicitApp _ f _ _)
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
    fixNames (IImplicitApp loc' f t a) = IImplicitApp loc' (fixNames f) t (fixNames a)
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
    updateLHS ups (IImplicitApp loc' f t a)
        = IImplicitApp loc' (updateLHS ups f) t (updateLHS ups a)
    updateLHS ups tm = tm

generateSplits : {auto m : Ref MD Metadata} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 FC -> Int -> ImpClause ->
                 Core (List (Name, List ImpClause))
generateSplits loc fn (ImpossibleClause fc lhs) = pure []
generateSplits loc fn (WithClause fc lhs wval flags cs) = pure []
generateSplits {c} {m} {u} loc fn (PatClause fc lhs rhs)
    = do (lhstm, _) <-
                elabTerm fn (InLHS linear) [] (MkNested []) []
                         (IBindHere loc PATTERN lhs) Nothing
         traverse (trySplit fc lhs lhstm rhs) (splittableNames lhs)

mutual
  tryAllSplits : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 FC -> Int -> Error ->
                 List (Name, List ImpClause) ->
                 Core (List ImpClause)
  tryAllSplits loc n err [] = throw err
  tryAllSplits loc n err ((x, []) :: rest)
      = tryAllSplits loc n err rest
  tryAllSplits loc n err ((x, cs) :: rest)
      = do log 5 $ "Splitting on " ++ show x
           catch (do cs' <- traverse (mkSplits loc n) cs
                     pure (concat cs'))
                 (\err => tryAllSplits loc n err rest)

  mkSplits : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             FC -> Int -> ImpClause ->
             Core (List ImpClause)
  -- If the clause works, use it. Otherwise, split on one of the splittable
  -- variables and try all of the resulting clauses
  mkSplits loc n c
      = catch (expandClause loc n c)
          (\err =>
              do cs <- generateSplits loc n c
                 log 5 $ "Splits: " ++ show cs
                 tryAllSplits loc n err cs)

export
makeDef : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          (FC -> (Name, Nat, ClosedTerm) -> Bool) ->
          Name -> Core (Maybe (FC, List ImpClause))
makeDef p n
    = do Just (loc, nidx, envlen, ty) <- findTyDeclAt p
            | Nothing => pure Nothing
         n <- getFullName nidx
         logTerm 5 ("Searching for " ++ show n) ty
         defs <- branch
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
             | Nothing => throw (UndefinedName loc n)
         cs' <- mkSplits loc nidx initcs
         -- restore the global state, given that we've fiddled with it a lot!
         put Ctxt defs
         put MD meta
         put UST ust
         pure (Just (loc, cs'))
