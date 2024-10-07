module Core.Coverage

import Core.Case.CaseTree
import Core.Case.Util
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import Data.List
import Data.Maybe
import Data.String

import Libraries.Data.NameMap
import Libraries.Data.String.Extra
import Libraries.Data.SnocList.SizeOf
import Libraries.Text.PrettyPrint.Prettyprinter

%default covering

-- Return whether any of the name matches conflict
conflictMatch : {vars : _} -> List (Name, Term vars) -> Bool
conflictMatch [] = False
conflictMatch ((x, tm) :: ms) = conflictArgs x tm ms || conflictMatch ms
  where
    data ClashResult = Distinct | Same | Incomparable

    clash : Term vars -> Term vars -> ClashResult
    clash (Ref _ (DataCon t _) _) (Ref _ (DataCon t' _) _)
        = if t /= t' then Distinct else Same
    clash (Ref _ (TyCon t _) _) (Ref _ (TyCon t' _) _)
        = if t /= t' then Distinct else Same
    clash (PrimVal _ c) (PrimVal _ c') = if  c /= c' then Distinct else Same
    clash (Ref _ t _) (PrimVal _ _) = if isJust (isCon t) then Distinct else Incomparable
    clash (PrimVal _ _) (Ref _ t _) = if isJust (isCon t) then Distinct else Incomparable
    clash (Ref _ t _) (TType _ _)   = if isJust (isCon t) then Distinct else Incomparable
    clash (TType _ _) (Ref _ t _)   = if isJust (isCon t) then Distinct else Incomparable
    clash (TType _ _) (PrimVal _ _) = Distinct
    clash (PrimVal _ _) (TType _ _) = Distinct
    clash _ _ = Incomparable

    findN : Nat -> Term vars -> Bool
    findN i (Local _ _ i' _) = i == i'
    findN i tm
        = let (Ref _ (DataCon _ _) _, args) = getFnArgs tm
                   | _ => False in
              any (findN i) args

    -- Assuming in normal form. Look for: mismatched constructors, or
    -- a name appearing strong rigid in the other term
    conflictTm : Term vars -> Term vars -> Bool
    conflictTm (Local _ _ i _) tm
        = let (Ref _ (DataCon _ _) _, args) = getFnArgs tm
                   | _ => False in
              any (findN i) args
    conflictTm tm (Local _ _ i _)
        = let (Ref _ (DataCon _ _) _, args) = getFnArgs tm
                   | _ => False in
              any (findN i) args
    conflictTm tm tm'
        = let (f, args) = getFnArgs tm
              (f', args') = getFnArgs tm' in
          case clash f f' of
            Distinct => True
            Incomparable => False
            Same => (any (uncurry conflictTm) (zip args args'))

    conflictArgs : Name -> Term vars -> List (Name, Term vars) -> Bool
    conflictArgs n tm [] = False
    conflictArgs n tm ((x, tm') :: ms)
        = (n == x && conflictTm tm tm') || conflictArgs n tm ms

-- Return whether any part of the type conflicts in such a way that they
-- can't possibly be equal (i.e. mismatched constructor)
conflict : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Defs -> Env Term vars -> NF vars -> Name -> Core Bool
conflict defs env nfty n
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure False
         case (definition gdef, type gdef) of
              (DCon t arity _, dty)
                  => do Nothing <- conflictNF 0 nfty !(nf defs [<] dty)
                            | Just ms => pure $ conflictMatch ms
                        pure True
              _ => pure False
  where
    mutual
      conflictArgs : Int -> SnocList (Closure vars) -> SnocList (Closure [<]) ->
                     Core (Maybe (List (Name, Term vars)))
      conflictArgs _ [<] [<] = pure (Just [])
      conflictArgs i (cs :< c) (cs' :< c')
          = do cnf <- evalClosure defs c
               cnf' <- evalClosure defs c'
               Just ms <- conflictNF i cnf cnf'
                    | Nothing => pure Nothing
               Just ms' <- conflictArgs i cs cs'
                    | Nothing => pure Nothing
               pure (Just (ms ++ ms'))
      conflictArgs _ _ _ = pure (Just [])

      -- If the constructor type (the NF [<]) matches the variable type,
      -- then there may be a way to construct it, so return the matches in
      -- the indices.
      -- If any of those matches clash, the constructor is not valid
      -- e.g, Eq x x matches Eq Z (S Z), with x = Z and x = S Z
      -- conflictNF returns the list of matches, for checking
      conflictNF : Int -> NF vars -> NF [<] ->
                   Core (Maybe (List (Name, Term vars)))
      conflictNF i t (NBind fc x b sc)
          -- invent a fresh name, in case a user has bound the same name
          -- twice somehow both references appear in the result  it's unlikely
          -- put possible
          = let x' = MN (show x) i in
                conflictNF (i + 1) t
                       !(sc defs (toClosure defaultOpts [<] (Ref fc Bound x')))
      conflictNF i nf (NApp _ (NRef Bound n) [<])
          = pure (Just [(n, !(quote defs env nf))])
      conflictNF i (NDCon _ n t a args) (NDCon _ n' t' a' args')
          = if t == t'
               then conflictArgs i (map snd args) (map snd args')
               else pure Nothing
      conflictNF i (NTCon _ n t a args) (NTCon _ n' t' a' args')
          = if n == n'
               then conflictArgs i (map snd args) (map snd args')
               else pure Nothing
      conflictNF i (NPrimVal _ c) (NPrimVal _ c')
          = if c == c'
               then pure (Just [])
               else pure Nothing
      conflictNF _ _ _ = pure (Just [])

-- Return whether the given type is definitely empty (due to there being
-- no constructors which can possibly match it.)
export
isEmpty : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          Defs -> Env Term vars -> NF vars -> Core Bool
isEmpty defs env (NTCon fc n t a args)
  = do Just nty <- lookupDefExact n (gamma defs)
         | _ => pure False
       case nty of
            TCon _ _ _ _ flags _ Nothing _ => pure False
            TCon _ _ _ _ flags _ (Just cons) _
                 => if not (external flags)
                       then allM (conflict defs env (NTCon fc n t a args)) cons
                       else pure False
            _ => pure False
isEmpty defs env _ = pure False

altMatch : CaseAlt vars -> CaseAlt vars -> Bool
altMatch _ (DefaultCase _) = True
altMatch (DelayCase _ _ t) (DelayCase _ _ t') = True
altMatch (ConCase n t _ _) (ConCase n' t' _ _) = t == t'
altMatch (ConstCase c _) (ConstCase c' _) = c == c'
altMatch _ _ = False

-- Given a type and a list of case alternatives, return the
-- well-typed alternatives which were *not* in the list
getMissingAlts : {auto c : Ref Ctxt Defs} ->
                 {vars : _} ->
                 FC -> Defs -> NF vars -> List (CaseAlt vars) ->
                 Core (List (CaseAlt vars))
-- If it's a primitive other than WorldVal, there's too many to reasonably
-- check, so require a catch all
getMissingAlts fc defs (NPrimVal _ $ PrT WorldType) alts
    = if isNil alts
         then pure [DefaultCase (Unmatched "Coverage check")]
         else pure []
getMissingAlts fc defs (NPrimVal _ c) alts
  = do log "coverage.missing" 50 $ "Looking for missing alts at type " ++ show c
       if any isDefault alts
         then do log "coverage.missing" 20 "Found default"
                 pure []
         else pure [DefaultCase (Unmatched "Coverage check")]
-- Similarly for types
getMissingAlts fc defs (NType _ _) alts
    = do log "coverage.missing" 50 "Looking for missing alts at type Type"
         if any isDefault alts
           then do log "coverage.missing" 20 "Found default"
                   pure []
           else pure [DefaultCase (Unmatched "Coverage check")]
getMissingAlts fc defs nfty alts
    = do log "coverage.missing" 50 $ "Getting constructors for: " ++ show nfty
         logNF "coverage.missing" 20 "Getting constructors for" (mkEnv fc _) nfty
         allCons <- getCons defs nfty
         pure (filter (noneOf alts)
                 (map (mkAlt fc (Unmatched "Coverage check")) allCons))
  where
    -- Return whether the alternative c matches none of the given cases in alts
    noneOf : List (CaseAlt vars) -> CaseAlt vars -> Bool
    noneOf alts c = not $ any (altMatch c) alts

-- Mapping of variable to constructor tag already matched for it
KnownVars : SnocList Name -> Type -> Type
KnownVars vars a = List (Var vars, a)

getName : {idx : Nat} -> {vars : SnocList Name} -> (0 p : IsVar n idx vars) -> Name
getName {vars = _ :< v} First = v
getName (Later p) = getName p

showK : {ns : _} ->
        Show a => KnownVars ns a -> String
showK {a} xs = show (map aString xs)
  where
    aString : {vars : Scope} ->
              (Var vars, a) -> (Name, a)
    aString (MkVar v, t) = (nameAt v, t)

weakenNs : SizeOf args -> KnownVars vars a -> KnownVars (vars ++ args) a
weakenNs args [] = []
weakenNs args ((v, t) :: xs)
  = (weakenNs args v, t) :: weakenNs args xs

findTag : {idx, vars : _} ->
          (0 p : IsVar n idx vars) -> KnownVars vars a -> Maybe a
findTag v [] = Nothing
findTag v ((v', t) :: xs)
    = if MkVar v == v'
         then Just t
         else findTag v xs

addNot : {idx, vars : _} ->
         (0 p : IsVar n idx vars) -> Int -> KnownVars vars (List Int) ->
         KnownVars vars (List Int)
addNot v t [] = [(MkVar v, [t])]
addNot v t ((v', ts) :: xs)
    = if MkVar v == v'
         then ((v', t :: ts) :: xs)
         else ((v', ts) :: addNot v t xs)

tagIsNot : List Int -> CaseAlt vars -> Bool
tagIsNot ts (ConCase _ t' _ _) = not (t' `elem` ts)
tagIsNot ts (ConstCase _ _) = True
tagIsNot ts (DelayCase _ _ _) = True
tagIsNot ts (DefaultCase _) = False

-- Replace a default case with explicit branches for the constructors.
-- This is easier than checking whether a default is needed when traversing
-- the tree (just one constructor lookup up front).
replaceDefaults : {auto c : Ref Ctxt Defs} ->
                  {vars : _} ->
                  FC -> Defs -> NF vars -> List (CaseAlt vars) ->
                  Core (List (CaseAlt vars))
-- Leave it alone if it's a primitive type though, since we need the catch
-- all case there
replaceDefaults fc defs (NPrimVal _ _) cs = pure cs
replaceDefaults fc defs (NType _ _) cs = pure cs
replaceDefaults fc defs nfty cs
    = do cs' <- traverse rep cs
         pure (dropRep (concat cs'))
  where
    rep : CaseAlt vars -> Core (List (CaseAlt vars))
    rep (DefaultCase sc)
        = do allCons <- getCons defs nfty
             pure (map (mkAlt fc sc) allCons)
    rep c = pure [c]

    dropRep : List (CaseAlt vars) -> List (CaseAlt vars)
    dropRep [] = []
    dropRep (c@(ConCase n t args sc) :: rest)
          -- assumption is that there's no defaultcase in 'rest' because
          -- we've just removed it
        = c :: dropRep (filter (not . tagIs t) rest)
    dropRep (c :: rest) = c :: dropRep rest

-- Traverse a case tree and refine the arguments while matching, so that
-- when we reach a leaf we know what patterns were used to get there,
-- and return those patterns.
-- The returned patterns are those arising from the *missing* cases
buildArgs : {auto c : Ref Ctxt Defs} ->
            {vars : _} ->
            FC -> Defs ->
            KnownVars vars Int -> -- Things which have definitely match
            KnownVars vars (List Int) -> -- Things an argument *can't* be
                                    -- (because a previous case matches)
            SnocList ClosedTerm -> -- ^ arguments, with explicit names
            CaseTree vars -> Core (List (SnocList ClosedTerm))
buildArgs fc defs known not ps cs@(Case {name = var} idx el ty altsIn)
  -- If we've already matched on 'el' in this branch, restrict the alternatives
  -- to the tag we already know. Otherwise, add missing cases and filter out
  -- the ones it can't possibly be (the 'not') because a previous case
  -- has matched.
    = do let fenv = mkEnv fc _
         nfty <- nf defs fenv ty
         alts <- replaceDefaults fc defs nfty altsIn
         let alts' = alts ++ !(getMissingAlts fc defs nfty alts)
         let altsK = maybe alts' (\t => filter (tagIs t) alts')
                              (findTag el known)
         let altsN = maybe altsK (\ts => filter (tagIsNot ts) altsK)
                              (findTag el not)
         buildArgsAlt not altsN
  where
    buildArgAlt : KnownVars vars (List Int) ->
                  CaseAlt vars -> Core (List (SnocList ClosedTerm))
    buildArgAlt not' (ConCase n t args sc)
        = do let l = mkSizeOf args
             let con = Ref fc (DataCon t (size l)) n
             let ps' = map (substName var
                             (apply fc
                                    con (toList $ map (Ref fc Bound) args))) ps
             buildArgs fc defs (weakenNs l ((MkVar el, t) :: known))
                               (weakenNs l not') ps' sc
    buildArgAlt not' (DelayCase t a sc)
        = let l = mkSizeOf [<a, t]
              ps' = map (substName var (TDelay fc LUnknown
                                             (Ref fc Bound t)
                                             (Ref fc Bound a))) ps in
              buildArgs fc defs (weakenNs l known) (weakenNs l not')
                                ps' sc
    buildArgAlt not' (ConstCase c sc)
        = do let ps' = map (substName var (PrimVal fc c)) ps
             buildArgs fc defs known not' ps' sc
    buildArgAlt not' (DefaultCase sc)
        = buildArgs fc defs known not' ps sc

    buildArgsAlt : KnownVars vars (List Int) -> List (CaseAlt vars) ->
                   Core (List (SnocList ClosedTerm))
    buildArgsAlt not' [] = pure []
    buildArgsAlt not' (c@(ConCase _ t _ _) :: cs)
        = pure $ !(buildArgAlt not' c) ++
                 !(buildArgsAlt (addNot el t not') cs)
    buildArgsAlt not' (c :: cs)
        = pure $ !(buildArgAlt not' c) ++ !(buildArgsAlt not' cs)

buildArgs fc defs known not ps (STerm _ vs)
    = pure [] -- matched, so return nothing
buildArgs fc defs known not ps (Unmatched msg)
    = pure [ps] -- unmatched, so return it
buildArgs fc defs known not ps Impossible
    = pure [] -- not a possible match, so return nothing

-- Traverse a case tree and return pattern clauses which are not
-- matched. These might still be invalid patterns, or patterns which are covered
-- elsewhere (turning up due to overlapping clauses) so the results should be
-- checked
export
getMissing : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             FC -> Name -> CaseTree vars ->
             Core (List ClosedTerm)
getMissing fc n ctree
   = do defs <- get Ctxt
        let psIn = map (Ref fc Bound) vars
        patss <- buildArgs fc defs [] [] psIn ctree
        let pats = concat patss
        unless (null pats) $
          logC "coverage.missing" 20 $ map (join "\n") $
            flip traverse pats $ \ pat =>
              show <$> toFullNames pat
        pure (map (apply fc (Ref fc Func n) . toList) patss)

-- For the given name, get the names it refers to which are not themselves
-- covering.
-- Also need to go recursively into case blocks, since we only calculate
-- references for them at the top level clause
export
getNonCoveringRefs : {auto c : Ref Ctxt Defs} ->
                     FC -> Name -> Core (List Name)
getNonCoveringRefs fc n
   = do defs <- get Ctxt
        Just d <- lookupCtxtExact n (gamma defs)
           | Nothing => undefinedName fc n
        let ds = mapMaybe noAssert (toList (refersTo d))
        let cases = filter isCase !(traverse toFullNames ds)

        -- Case blocks aren't recursive, so we're safe!
        cbad <- traverse (getNonCoveringRefs fc) cases
        topbad <- filterM (notCovering defs) ds
        pure (topbad ++ concat cbad)
  where
    isCase : Name -> Bool
    isCase (NS _ n) = isCase n
    isCase (CaseBlock _ _) = True
    isCase _ = False

    noAssert : (Name, Bool) -> Maybe Name
    noAssert (n, True) = Nothing
    noAssert (n, False) = Just n

    notCovering : Defs -> Name -> Core Bool
    notCovering defs n
        = case !(lookupCtxtExact n (gamma defs)) of
               Just def => case isCovering (totality def) of
                                IsCovering => pure False
                                _ => pure True
               _ => pure False

-- Does the second term match against the first?
-- 'Erased' matches against anything, we assume that's a Rig0 argument that
-- we don't care about
match : Term vs -> Term vs -> Bool
match (Local _ _ i _) _ = True
match (Ref _ Bound n) _ = True
match (Ref _ _ n) (Ref _ _ n') = n == n'
match (App _ f a) (App _ f' a') = match f f' && match a a'
match (As _ _ _ p) (As _ _ _ p') = match p p'
match (As _ _ _ p) p' = match p p'
match (TDelayed _ _ t) (TDelayed _ _ t') = match t t'
match (TDelay _ _ _ t) (TDelay _ _ _ t') = match t t'
match (TForce _ _ t) (TForce _ _ t') = match t t'
match (PrimVal _ c) (PrimVal _ c') = c == c'
match (Erased _ (Dotted t)) u = match t u
match t (Erased _ (Dotted u)) = match t u
match (Erased _ _) _ = True
match _ (Erased _ _) = True
match (TType _ _) (TType _ _) = True
match _ _ = False

-- Erase according to argument position
eraseApps : {auto c : Ref Ctxt Defs} ->
            Term vs -> Core (Term vs)
eraseApps {vs} tm
    = case getFnArgsSpine tm of
           (Ref fc Bound n, args) =>
                do args' <- traverseSnocList eraseApps args
                   pure (applySpine fc (Ref fc Bound n) args')
           (Ref fc nt n, args) =>
                do defs <- get Ctxt
                   mgdef <- lookupCtxtExact n (gamma defs)
                   let eargs = maybe [] eraseArgs mgdef
                   args' <- traverseSnocList eraseApps (dropPos fc 0 eargs args)
                   pure (applySpine fc (Ref fc nt n) args')
           (tm, args) =>
                do args' <- traverseSnocList eraseApps args
                   pure (applySpine (getLoc tm) tm args')
  where
    dropPos : FC -> Nat -> List Nat -> SnocList (Term vs) -> SnocList (Term vs)
    dropPos fc i ns [<] = [<]
    dropPos fc i ns (xs :< x)
        = if i `elem` ns
             then dropPos fc (S i) ns xs :< Erased fc Placeholder
             else dropPos fc (S i) ns xs :< x

-- if tm would be matched by trylhs, then it's not an impossible case
-- because we've already got it. Ignore anything in erased position.
clauseMatches : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Env Term vars -> Term vars ->
                ClosedTerm -> Core Bool
clauseMatches env tm trylhs
    = let lhs = !(eraseApps (close (getLoc tm) "cov" env tm)) in
          pure $ match !(toResolvedNames lhs) !(toResolvedNames trylhs)

export
checkMatched : {auto c : Ref Ctxt Defs} ->
               List Clause -> ClosedTerm -> Core (Maybe ClosedTerm)
checkMatched cs ulhs
    = do logTerm "coverage" 5 "Checking coverage for" ulhs
         logC "coverage" 10 $ pure $ "(raw term: " ++ show !(toFullNames ulhs) ++ ")"
         ulhs <- eraseApps ulhs
         logTerm "coverage" 5 "Erased to" ulhs
         logC "coverage" 5 $ do
            cs <- traverse toFullNames cs
            pure $ "Against clauses:\n" ++
                   (show $ indent 2 $ vcat $ map (pretty . show) cs)
         tryClauses cs ulhs
  where
    tryClauses : List Clause -> ClosedTerm -> Core (Maybe ClosedTerm)
    tryClauses [] ulhs
        = do logTermNF "coverage" 10 "Nothing matches" [<] ulhs
             pure $ Just ulhs
    tryClauses (MkClause env lhs _ :: cs) ulhs
        = if !(clauseMatches env lhs ulhs)
             then do logTermNF "coverage" 10 "Yes" env lhs
                     pure Nothing -- something matches, discared it
             else do logTermNF "coverage" 10 "No match" env lhs
                     tryClauses cs ulhs
