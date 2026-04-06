module Core.Case.CaseBuilder

import Core.Case.CaseTree
import Core.Case.Util
import Core.Context.Log
import Core.Env
import Core.Options
import Core.Evaluate.Value
import Core.Evaluate.Quote
import Core.Evaluate.Normalise
import Core.Evaluate.Expand
import Core.Evaluate

import Idris.Pretty.Annotations

import Data.DPair
import Data.SnocList.Quantifiers
import Data.SortedSet
import Data.String
import Data.Vect
import Data.List.HasLength

import Libraries.Data.List.LengthMatch
import Libraries.Data.List01
import Libraries.Data.List01.Quantifiers
import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.Quantifiers.Extra as Lib
import Libraries.Data.SnocList.SizeOf
import Libraries.Text.PrettyPrint.Prettyprinter

import Decidable.Equality

%default covering

%hide Symbols.equals

public export
data Phase = CompileTime RigCount | RunTime

Eq Phase where
  CompileTime r == CompileTime r' = r == r'
  RunTime == RunTime = True
  _ == _ = False

data ArgType : Scoped where
     Known : RigCount -> (ty : Term vars) -> ArgType vars -- arg has type 'ty'
     Stuck : (fty : Term vars) -> ArgType vars
         -- ^ arg will have argument type of 'fty' when we know enough to
         -- calculate it
     Unknown : ArgType vars
         -- arg's type is not yet known due to a previously stuck argument

HasNames (ArgType vars) where
  full gam (Known c ty) = Known c <$> full gam ty
  full gam (Stuck ty) = Stuck <$> full gam ty
  full gam Unknown = pure Unknown

  resolved gam (Known c ty) = Known c <$> resolved gam ty
  resolved gam (Stuck ty) = Stuck <$> resolved gam ty
  resolved gam Unknown = pure Unknown

covering
{ns : _} -> Show (ArgType ns) where
  show (Known c t) = "Known " ++ show c ++ " " ++ show t
  show (Stuck t) = "Stuck " ++ show t
  show Unknown = "Unknown"

record PatInfo (pvar : Name) (vars : Scope) where
  constructor MkInfo
  {idx : Nat}
  {name : Name}
  multiplicity : RigCount -- Cached for using in the 'Case' block
  pat : Pat
  0 loc : IsVar name idx vars
  argType : ArgType vars -- Type of the argument being inspected (i.e.
                         -- *not* refined by this particular pattern)

covering
{vars : _} -> Show (PatInfo n vars) where
  show pi = show (pat pi) ++ " : " ++ show (argType pi)

HasNames (PatInfo n vars) where
  full gam (MkInfo c pat loc argType)
     = do pat <- full gam pat
          argType <- full gam argType
          pure $ MkInfo c pat loc argType

  resolved gam (MkInfo c pat loc argType)
     = do pat <- resolved gam pat
          argType <- resolved gam argType
          pure $ MkInfo c pat loc argType

{-
NamedPats is a list of patterns on the LHS of a clause. Each entry in
the list gives a pattern, and a proof that there is a variable we can
inspect to see if it matches the pattern.

A definition consists of a list of clauses, which are a 'NamedPats' and
a term on the RHS. There is an assumption that corresponding positions in
NamedPats always have the same 'Elem' proof, though this isn't expressed in
a type anywhere.
-}

-- TODO: All
-- NamedPats : List Name -> -- the pattern variables still to process,
--                          -- in order
--             Scoped
-- NamedPats vars
--   = All (\pvar => PatInfo pvar vars)
--                -- ^ a pattern, where its variable appears in the vars list,
--                -- and its type. The type has no variable names; any names it
--                -- refers to are explicit
data NamedPats : List Name -> -- the pattern variables still to process,
                              -- in order
                 Scoped where
     Nil : NamedPats [] vars
     (::) : PatInfo pvar vars ->
            -- ^ a pattern, where its variable appears in the vars list,
            -- and its type. The type has no variable names; any names it
            -- refers to are explicit
            NamedPats ns vars -> NamedPats (pvar :: ns) vars

getPatInfo : NamedPats todo vars -> List Pat
getPatInfo [] = []
getPatInfo (x :: xs) = pat x :: getPatInfo xs

updatePats : {vars, todo : _} ->
             {auto c : Ref Ctxt Defs} ->
             Env Term vars ->
             NF vars -> NamedPats todo vars -> Core (NamedPats todo vars)
updatePats env nf [] = pure []
updatePats {todo = pvar :: ns} env (VBind fc _ (Pi _ c _ farg) fsc) (p :: ps)
  = case argType p of
         Unknown =>
            do defs <- get Ctxt
               empty <- clearDefs defs
               fsc' <- expand !(fsc (pure (vRef fc Bound pvar)))
               pure ({ argType := Known c !(quote env farg) } p
                          :: !(updatePats env fsc' ps))
         _ => pure (p :: ps)
updatePats env nf (p :: ps)
  = case argType p of
         Unknown =>
            do defs <- get Ctxt
               empty <- clearDefs defs
               pure ({ argType := Stuck !(quote env nf) } p :: ps)
         _ => pure (p :: ps)

substInPatInfo : {pvar, vars, todo : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Term vars -> PatInfo pvar vars ->
                 NamedPats todo vars ->
                 Core (PatInfo pvar vars, NamedPats todo vars)
substInPatInfo {pvar} {vars} fc n tm p ps
    = case argType p of
           Known c ty =>
                do defs <- get Ctxt
                   logTerm "compile.casetree" 25 "substInPatInfo-Known-tm" tm
                   logTerm "compile.casetree" 25 "substInPatInfo-Known-ty" ty
                   log "compile.casetree" 25 $ "n: " ++ show n
                   -- let env = mkEnv fc vars
                   --  logEnvRev "compile.casetree" 25 "substInPatInfo env" env
                   tynf <- nf (mkEnv fc _) ty
                   case tynf of
                        VApp{} =>
                           pure ({ argType := Known c (substName zero n tm ty) } p, ps)
                        VMeta{} =>
                           pure ({ argType := Known c (substName zero n tm ty) } p, ps)
                        VLocal{} =>
                           pure ({ argType := Known c (substName zero n tm ty) } p, ps)
                        -- Got a concrete type, and that's all we need, so stop
                        _ => pure (p, ps)
           Stuck fty =>
             do defs <- get Ctxt
                empty <- clearDefs defs
                let env = mkEnv fc vars
                case !(nf env (substName zero n tm fty)) of
                     VBind pfc _ (Pi _ c _ farg) fsc =>
                       do fsc' <- expand !(fsc (pure (vRef pfc Bound pvar)))
                          pure ({ argType := Known c !(quote env farg) } p,
                                 !(updatePats env fsc' ps))
                     _ => pure (p, ps)
           Unknown => pure (p, ps)

-- Substitute the name with a term in the pattern types, and reduce further
-- (this aims to resolve any 'Stuck' pattern types)
substInPats : {vars, todo : _} ->
              {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Term vars -> NamedPats todo vars ->
              Core (NamedPats todo vars)
substInPats fc n tm [] = pure []
substInPats fc n tm (p :: ps)
    = do (p', ps') <- substInPatInfo fc n tm p ps
         pure (p' :: !(substInPats fc n tm ps'))

getPat : {idx : Nat} ->
         (0 el : IsVarL nm idx ps) -> NamedPats ps ns -> PatInfo nm ns
getPat First (x :: xs) = x
getPat (Later p) (x :: xs) = getPat p xs

dropPat : {idx : Nat} ->
          (0 el : IsVarL nm idx ps) ->
          NamedPats ps ns -> NamedPats (dropIsVarL ps el) ns
dropPat First (x :: xs) = xs
dropPat (Later p) (x :: xs) = x :: dropPat p xs

HasNames (NamedPats todo vars) where
  full gam [] = pure []
  full gam (x::xs) = [| (::) (full gam x) (full gam xs) |]

  resolved gam [] = pure []
  resolved gam (x::xs) = [| (::) (resolved gam x) (resolved gam xs) |]

covering
{vars : _} -> {todo : _} -> Show (NamedPats todo vars) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : {vs, ts : _} -> NamedPats ts vs -> String
      showAll [] = ""
      showAll {ts = t :: _} [x]
          = show t ++ " " ++ show (pat x) ++ " [" ++ show (argType x) ++ "]"
      showAll {ts = t :: _} (x :: xs)
          = show t ++ " " ++ show (pat x) ++ " [" ++ show (argType x) ++ "]"
                     ++ ", " ++ showAll xs

{vars : _} -> {todo : _} -> Pretty IdrisSyntax (NamedPats todo vars) where
  pretty xs = hsep $ prettyAll xs
    where
      prettyAll : {vs, ts : _} -> NamedPats ts vs -> List (Doc IdrisSyntax)
      prettyAll [] = []
      prettyAll {ts = t :: _} (x :: xs)
          = parens (pretty0 t <++> equals <++> pretty (pat x))
          :: prettyAll xs

Weaken ArgType where
  weaken (Known c ty) = Known c (weaken ty)
  weaken (Stuck fty) = Stuck (weaken fty)
  weaken Unknown = Unknown

  weakenNs s (Known c ty) = Known c (weakenNs s ty)
  weakenNs s (Stuck fty) = Stuck (weakenNs s fty)
  weakenNs s Unknown = Unknown

GenWeaken ArgType where
  genWeakenNs p q Unknown = Unknown
  genWeakenNs p q (Known c ty) = Known c $ genWeakenNs p q ty
  genWeakenNs p q (Stuck fty) = Stuck $ genWeakenNs p q fty

Weaken (PatInfo p) where
  weaken (MkInfo c p el fty) = MkInfo c p (Later el) (weaken fty)

Weaken (NamedPats todo) where
  weaken [] = []
  weaken (p :: ps) = weaken p :: weaken ps

  weakenNs ns [] = []
  weakenNs ns (p :: ps) = weakenNs ns p :: weakenNs ns ps

FreelyEmbeddable (PatInfo p) where

FreelyEmbeddable (NamedPats todo) where
  embed [] = []
  embed (x :: xs) = embed x :: embed xs

FreelyEmbeddable ArgType where
  embed Unknown = Unknown
  embed (Stuck t) = Stuck (embed t)
  embed (Known c t) = Known c (embed t)

GenWeaken (PatInfo p) where
  genWeakenNs p q (MkInfo c pat loc at) = do
    let MkNVar loc' = genWeakenNs p q $ MkNVar loc
    let at' = genWeakenNs p q at
    MkInfo c pat loc' at'

GenWeaken (NamedPats todo) where
  genWeakenNs p q [] = []
  genWeakenNs p q  (pi :: np) = genWeakenNs p q pi :: genWeakenNs p q np

(++) : NamedPats ms vars -> NamedPats ns vars -> NamedPats (ms ++ ns) vars
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

tail : NamedPats (p :: ps) vars -> NamedPats ps vars
tail (x :: xs) = xs

-- If a pattern variable appears more than once, it means there will be some
-- forced equalities between variables bound in case branches, so record the
-- equalities as we go
record PMappings vars where
  constructor MkPMappings
  pvars : List (Name, Var vars) -- What each pattern variable matched
  pforced : List (Var vars, Term vars) -- Forced equalities

Weaken PMappings where
  weakenNs s
      = { pvars $= map (\ (n, t) => (n, weakenNs s t)),
          pforced $= map (\ (l, r) => (weakenNs s l, weakenNs s r)) }

-- Substitute all the pattern variables into the right terms in the forced
-- equalities
substForced : List (Name, Var vars) -> List (Var vars, Term vars) ->
              List (Var vars, Term vars)
substForced [] eqs = eqs
substForced ((n, MkVar v) :: ns) eqs
    = let eqs' = map (substInForced n (Local EmptyFC Nothing _ v)) eqs in
          substForced ns eqs'
  where
    substInForced : Name -> Term vars -> (Var vars, Term vars) ->
                    (Var vars, Term vars)
    substInForced n ptm (v, tm) = (v, substName zero n ptm tm)

covering
{vars : _} -> Show (PMappings vars) where
  show pmaps
      = "Pattern variables: " ++ joinBy ", " (map showPVar (pvars pmaps)) ++ "\t" ++
        "Forced equalities: " ++ joinBy ", " (map showForced (pforced pmaps))
    where
      showPVar : (Name, Var vars) -> String
      showPVar (n, MkVar v) = show n ++ ": " ++ show (Local EmptyFC Nothing _ v)

      showForced : (Var vars, Term vars) -> String
      showForced (MkVar v, tm) = show (Local EmptyFC Nothing _ v) ++ " = " ++ show tm

HasNames (PMappings vars) where
  full gam (MkPMappings pvars pforced)
     = pure $ MkPMappings pvars
                  !(traverse (\ (n, t) => pure (n, !(full gam t))) pforced)
  resolved gam (MkPMappings pvars pforced)
     = pure $ MkPMappings pvars
                  !(traverse (\ (n, t) => pure (n, !(resolved gam t))) pforced)

initPMap : PMappings vars
initPMap = MkPMappings [] []

data PatClause : (todo : List Name) -> Scoped where
     MkPatClause : List Name -> -- names matched so far (from original lhs)
                   PMappings vars ->
                   NamedPats todo vars ->
                   Int -> (rhs : Term vars) -> PatClause todo vars

getNPs : PatClause todo vars -> NamedPats todo vars
getNPs (MkPatClause _ _ lhs pid rhs) = lhs

covering
{vars : _} -> {todo : _} -> Show (PatClause todo vars) where
  show (MkPatClause _ pmaps ps pid rhs)
     = show ps ++ " => " ++ show pmaps ++ " " ++ show rhs

{vars : _} -> {todo : _} -> Pretty IdrisSyntax (PatClause todo vars) where
  pretty (MkPatClause _ _ ps _ rhs)
     = pretty ps <++> fatArrow <++> byShow rhs

HasNames (PatClause todo vars) where
  full gam (MkPatClause ns pmaps nps i rhs)
     = [| MkPatClause (traverse (full gam) ns)
                      (full gam pmaps)
                      (full gam nps) (pure i) (full gam rhs) |]

  resolved gam (MkPatClause ns pmaps nps i rhs)
     = [| MkPatClause (traverse (resolved gam) ns)
                      (resolved gam pmaps)
                      (resolved gam nps) (pure i) (resolved gam rhs) |]

substInClause : {a, vars, todo : _} ->
                {auto c : Ref Ctxt Defs} ->
                FC -> PatClause (a :: todo) vars ->
                Core (PatClause (a :: todo) vars)
substInClause {vars} {a} fc (MkPatClause pvars pmaps (MkInfo c pat pprf fty :: pats) pid rhs)
    = do let tm = mkTerm vars pat
         log "compile.casetree.subst" 50 "Substituting \{show tm} for \{show a} in \{show pat}"
         pats' <- substInPats fc a tm pats
         pure (MkPatClause pvars pmaps (MkInfo c pat pprf fty :: pats') pid rhs)

data Partitions : List (PatClause todo vars) -> Type where
     ConClauses : {todo, vars, ps : _} ->
                  (cs : List (PatClause todo vars)) ->
                  Partitions ps -> Partitions (cs ++ ps)
     VarClauses : {todo, vars, ps : _} ->
                  (vs : List (PatClause todo vars)) ->
                  Partitions ps -> Partitions (vs ++ ps)
     NoClauses : Partitions []

covering
{ps : _} -> Show (Partitions ps) where
  show (ConClauses cs rest)
    = unlines ("CON" :: map (("  " ++) . show) cs)
    ++ "\n, " ++ show rest
  show (VarClauses vs rest)
    = unlines ("VAR" :: map (("  " ++) . show) vs)
    ++ "\n, " ++ show rest
  show NoClauses = "NONE"

data ClauseType = ConClause | VarClause

namesIn : List Name -> Pat -> Bool
namesIn pvars (PAs _ n p) = (n `elem` pvars) && namesIn pvars p
namesIn pvars (PCon _ _ _ _ ps) = all (namesIn pvars) (map snd ps)
namesIn pvars (PTyCon _ _ _ ps) = all (namesIn pvars) (map snd ps)
namesIn pvars (PArrow _ _ s t) = namesIn pvars s && namesIn pvars t
namesIn pvars (PDelay _ _ t p) = namesIn pvars t && namesIn pvars p
namesIn pvars (PLoc _ n) = n `elem` pvars
namesIn pvars _ = True

namesFrom : Pat -> List Name
namesFrom (PAs _ n p) = n :: namesFrom p
namesFrom (PCon _ _ _ _ ps) = concatMap namesFrom (map snd ps)
namesFrom (PTyCon _ _ _ ps) = concatMap namesFrom (map snd ps)
namesFrom (PArrow _ _ s t) = namesFrom s ++ namesFrom t
namesFrom (PDelay _ _ t p) = namesFrom t ++ namesFrom p
namesFrom (PLoc _ n) = [n]
namesFrom _ = []

clauseType : Phase -> PatClause (a :: as) vars -> ClauseType
-- If it's irrelevant, a constructor, and there's no names we haven't seen yet
-- and don't see later, treat it as a variable
-- Or, if we're compiling for runtime we won't be able to split on it, so
-- also treat it as a variable
-- Or, if it's an under-applied constructor then do NOT attempt to split on it!
clauseType phase (MkPatClause pvars pmaps (MkInfo _ arg _ ty :: rest) pid rhs)
    = getClauseType phase arg ty
  where
    -- used when we are tempted to split on a constructor: is
    -- this actually a fully applied one?
    splitCon : Nat -> SnocList (RigCount, Pat) -> ClauseType
    splitCon arity xs
      = if arity == length xs then ConClause else VarClause

    -- used to get the remaining clause types
    clauseType' : Pat -> ClauseType
    clauseType' (PCon _ _ _ a xs) = splitCon a xs
    clauseType' (PTyCon _ _ a xs) = splitCon a xs
    clauseType' (PConst _ x)      = ConClause
    clauseType' (PArrow _ _ s t)  = ConClause
    clauseType' (PDelay _ _ _ _)  = ConClause
    clauseType' _                 = VarClause

    getClauseType : Phase -> Pat -> ArgType vars -> ClauseType
    getClauseType (CompileTime cr) (PCon _ _ _ a xs) (Known r t)
        = if (isErased r && not (isErased cr) &&
             all (namesIn (pvars ++ concatMap namesFrom (getPatInfo rest))) (map snd xs))
             then VarClause
             else splitCon a xs
    getClauseType phase (PAs _ _ p) t = getClauseType phase p t
    getClauseType phase l (Known r t) = if isErased r
      then VarClause
      else clauseType' l
    getClauseType phase l _ = clauseType' l

partition : {a, as, vars : _} ->
            Phase -> (ps : List (PatClause (a :: as) vars)) -> Partitions ps
partition phase [] = NoClauses
partition phase (x :: xs) with (partition phase xs)
  partition phase (x :: (cs ++ ps)) | (ConClauses cs rest)
        = case clauseType phase x of
               ConClause => ConClauses (x :: cs) rest
               VarClause => VarClauses [x] (ConClauses cs rest)
  partition phase (x :: (vs ++ ps)) | (VarClauses vs rest)
        = case clauseType phase x of
               ConClause => ConClauses [x] (VarClauses vs rest)
               VarClause => VarClauses (x :: vs) rest
  partition phase (x :: []) | NoClauses
        = case clauseType phase x of
               ConClause => ConClauses [x] NoClauses
               VarClause => VarClauses [x] NoClauses

data ConType : Type where
     CName : Name -> (tag : Int) -> ConType
     CDelay : ConType
     CConst : Constant -> ConType

data Group : List Name -> -- pattern variables still to process
             Scoped where
     ConGroup : {newargs : _} ->
                Name -> (tag : Int) ->
                List RigCount -> -- Cached from constructor type
                List (PatClause (newargs ++ todo) (vars <>< newargs)) ->
                Group todo vars
     DelayGroup : {tyarg, valarg : _} ->
                  List (PatClause (tyarg :: valarg :: todo)
                                  (vars :< tyarg :< valarg)) ->
                  Group todo vars
     ConstGroup : Constant -> List (PatClause todo vars) ->
                  Group todo vars

covering
{vars : _} -> {todo : _} -> Show (Group todo vars) where
  show (ConGroup c t _ cs) = "Con " ++ show c ++ ": " ++ show cs
  show (DelayGroup cs) = "Delay: " ++ show cs
  show (ConstGroup c cs) = "Const " ++ show c ++ ": " ++ show cs

data GroupMatch : ConType -> List (RigCount, Pat) -> Group todo vars -> Type where
  ConMatch : {tag : Int} -> (0 _ : LengthMatch ps newargs) ->
             GroupMatch (CName n tag) ps
               (ConGroup {newargs} n tag rigs (MkPatClause pvs pmaps pats pid rhs :: rest))
  DelayMatch : GroupMatch CDelay []
               (DelayGroup {tyarg} {valarg} (MkPatClause pvs pmaps pats pid rhs :: rest))
  ConstMatch : GroupMatch (CConst c) []
                  (ConstGroup c (MkPatClause pvs pmaps pats pid rhs :: rest))
  NoMatch : GroupMatch ct ps g

checkGroupMatch : (c : ConType) -> (ps : List (RigCount, Pat)) -> (g : Group todo vars) ->
                  GroupMatch c ps g
checkGroupMatch (CName x tag) ps (ConGroup {newargs} x' tag' rigs
                                           (MkPatClause pvs pmaps pats pid rhs :: rest))
    = case checkLengthMatch ps newargs of
           Nothing => NoMatch
           Just prf => case (nameEq x x', decEq tag tag') of
                            (Just Refl, Yes Refl) => ConMatch prf
                            _ => NoMatch
checkGroupMatch (CName x tag) ps _ = NoMatch
checkGroupMatch CDelay [] (DelayGroup (MkPatClause pvs pmaps pats pid rhs :: rest))
    = DelayMatch
checkGroupMatch (CConst c) [] (ConstGroup c' (MkPatClause pvs pmaps pats pid rhs :: rest))
    = case constantEq c c' of
           Nothing => NoMatch
           Just Refl => ConstMatch
checkGroupMatch _ _ _ = NoMatch

data PName : Type where

nextName : {auto i : Ref PName Int} ->
           String -> Core Name
nextName root
    = do x <- get PName
         put PName (x + 1)
         pure (MN root x)

getArgTys : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            Env Term vars -> List Name -> NF vars -> Core (List (ArgType vars))
getArgTys env (n :: ns) (VBind pfc _ (Pi _ c _ farg) fsc)
    = do rest <- getArgTys env ns !(expand !(fsc (pure (vRef pfc Bound n))))
         pure (Known c !(quote env farg) :: rest)
getArgTys env (n :: ns) t
      -- pad with 'Unknown' so we have the right arity
    = pure (Stuck !(quote env t) :: map (const Unknown) ns)
getArgTys _ _ _ = pure []

nextNames' : RigCount ->
             (pats : List (RigCount, Pat)) ->
             (ns : List Name) ->
             (0 _ : LengthMatch pats ns) ->
             List (ArgType vars) ->
             (args ** (SizeOf args, NamedPats args (vars <>< args)))
nextNames' rig [] [] NilMatch _ = ([] ** (zero, []))
nextNames' rig ((c, p) :: pats) (n :: ns) (ConsMatch prf) as
  = do let (ty, as) : (ArgType (vars :< n), List (ArgType vars))
           := case as of
                [] => (Unknown, [])
                (a :: as) => (weaken a, as)
       let (args ** (l, ps)) = nextNames' rig pats ns prf as
       (n :: args ** (suc l, weakensN l (MkInfo (rigMult rig c) p First ty) :: genWeakenFishily l ps))

nextNames : {vars : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            RigCount -> FC -> String -> List (RigCount, Pat) -> NF vars ->
            Core (args ** (SizeOf args, NamedPats args (Scope.ext vars args)))
nextNames _ _ _ [] _ = pure ([] ** (zero, []))
nextNames {vars} rig fc root pats nty
     = do (Element args p) <- mkNames pats
          let env = mkEnv fc vars
          argTys <- logQuiet $ getArgTys env args nty
          pure $ nextNames' rig pats args p argTys
  where
    mkNames : (vars : List a) -> Core $ Subset (List Name) (LengthMatch vars)
    mkNames [] = pure (Element [] NilMatch)
    mkNames (x :: xs)
        = do n <- nextName root
             (Element ns p) <- mkNames xs
             pure $ Element (n :: ns) (ConsMatch p)

-- replace the prefix of patterns with 'pargs'
newPats : (pargs : List (RigCount, Pat)) -> (0 _ : LengthMatch pargs ns) ->
          NamedPats (ns ++ todo) vars ->
          NamedPats ns vars
newPats [] NilMatch rest = []
newPats ((c, newpat) :: xs) (ConsMatch w) (pi :: rest)
  = { multiplicity := c
    , pat := newpat } pi :: newPats xs w rest

updateNames : List (Name, Pat) -> List (Name, Name)
updateNames = mapMaybe update
  where
    update : (Name, Pat) -> Maybe (Name, Name)
    update (n, PLoc fc p) = Just (p, n)
    update _ = Nothing

updatePatNames : List (Name, Name) -> NamedPats todo vars -> NamedPats todo vars
updatePatNames _ [] = []
updatePatNames ns (pi :: ps)
    = { pat $= update } pi :: updatePatNames ns ps
  where
    update : Pat -> Pat
    update (PAs fc n p)
        = case lookup n ns of
               Nothing => PAs fc n (update p)
               Just n' => PAs fc n' (update p)
    update (PCon fc n i a ps) = PCon fc n i a (map @{Compose} update ps)
    update (PTyCon fc n a ps) = PTyCon fc n a (map @{Compose} update ps)
    update (PArrow fc x s t) = PArrow fc x (update s) (update t)
    update (PDelay fc r t p) = PDelay fc r (update t) (update p)
    update (PLoc fc n)
        = case lookup n ns of
               Nothing => PLoc fc n
               Just n' => PLoc fc n'
    update p = p

groupCons : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto ct : Ref Ctxt Defs} ->
            FC -> Name ->
            List Name ->
            List (PatClause (a :: todo) vars) ->
            Core (List (Group todo vars))
groupCons fc fn pvars cs
     = gc [] cs
  where
    addConG : {vars', todo' : _} ->
              RigCount -> Name -> (tag : Int) ->
              List (RigCount, Pat) -> NamedPats todo' vars' ->
              PMappings vars' -> Int -> (rhs : Term vars') ->
              (acc : List (Group todo' vars')) ->
              Core (List (Group todo' vars'))
    -- Group all the clauses that begin with the same constructor, and
    -- add new pattern arguments for each of that constructor's arguments.
    -- The type of 'ConGroup' ensures that we refer to the arguments by
    -- the same name in each of the clauses
    addConG {vars'} {todo'} rig n tag pargs pats pmaps pid rhs []
        = do cty <- if n == UN (Basic "->")
                      then pure $ VBind fc (MN "_" 0) (Pi fc top Explicit (VType fc (MN "top" 0))) $
                              (\a => pure $ VBind fc (MN "_" 1) (Pi fc top Explicit (VErased fc Placeholder))
                                (\a => pure $ VType fc (MN "top" 0)))
                      else do defs <- get Ctxt
                              Just t <- lookupTyExact n (gamma defs)
                                   | Nothing => pure (VErased fc Placeholder)
                              expand !(nf (mkEnv fc vars') (embed t))
             (patnames ** (l, newargs)) <- logDepth $ do
                log "compile.casetree" 25 $ "addConG nextNames for " ++ show pargs
                logNF "compile.casetree" 25 "addConG nextNames cty" (mkEnv fc vars') cty
                nextNames {vars=vars'} rig fc "e" pargs cty
             log "compile.casetree" 25 $ "addConG patnames  " ++ show patnames
             log "compile.casetree" 25 $ "addConG newargs  " ++ show newargs
             -- Update non-linear names in remaining patterns (to keep
             -- explicit dependencies in types accurate)
             let pats' = updatePatNames (updateNames (zip patnames (map snd pargs)))
                                        (weakensN l pats)
             let clause = MkPatClause pvars (weakensN l pmaps)
                                      (newargs ++ pats') pid (weakensN l rhs)
             pure [ConGroup n tag (map fst pargs) [clause]]
    addConG {vars'} {todo'} rig n tag pargs pats pmaps pid rhs (g :: gs) with (checkGroupMatch (CName n tag) pargs g)
      addConG {vars'} {todo'} _ n tag pargs pats pmaps pid rhs
              ((ConGroup {newargs} n tag rigs ((MkPatClause pvars pmaps' ps tid tm) :: rest)) :: gs)
                   | (ConMatch {newargs} lprf)
        = do let newps = newPats pargs lprf ps
             let l = mkSizeOf newargs
             let pats' = updatePatNames (updateNames (zip newargs (map snd pargs)))
                                        (weakensN l pats)
             let newclause = MkPatClause pvars (weakensN l pmaps)
                                         (newps ++ pats') pid (weakensN l rhs)
             -- put the new clause at the end of the group, since we
             -- match the clauses top to bottom.
             pure ((ConGroup n tag rigs (MkPatClause pvars pmaps' ps tid tm :: rest ++ [newclause]))
                         :: gs)
      addConG rig n tag pargs pats pmaps pid rhs (g :: gs) | NoMatch
        = do gs' <- addConG rig n tag pargs pats pmaps pid rhs gs
             pure (g :: gs')

    -- This rather ugly special case is to deal with laziness, where Delay
    -- is like a constructor, but with a special meaning that it forces
    -- evaluation when case analysis reaches it (dealt with in the evaluator
    -- and compiler)
    addDelayG : {vars', todo' : _} ->
                Pat -> Pat -> NamedPats todo' vars' ->
                PMappings vars' -> Int -> (rhs : Term vars') ->
                (acc : List (Group todo' vars')) ->
                Core (List (Group todo' vars'))
    addDelayG {vars'} {todo'} pty parg pats pmaps pid rhs []
        = do let dty = VBind fc (MN "a" 0) (Pi fc erased Explicit (VType fc (MN "top" 0))) $
                        (\a => do a'<- a
                                  pure (VBind fc (MN "x" 0) (Pi fc top Explicit a')
                                           (\av => pure (VDelayed fc LUnknown a'))))
             ([tyname, argname] ** (l, newargs)) <- nextNames {vars=vars'} top fc "e" [(top, pty), (top, parg)] dty
                | _ => throw (InternalError "Error compiling Delay pattern match")
             let pats' = updatePatNames (updateNames [(tyname, pty), (argname, parg)])
                                        (weakensN l pats)
             let clause = MkPatClause pvars (weakensN l pmaps)
                                      (newargs ++ pats') pid (weakensN l rhs)
             pure [DelayGroup [clause]]
    addDelayG {vars'} {todo'} pty parg pats pmaps pid rhs (g :: gs) with (checkGroupMatch CDelay [] g)
      addDelayG {vars'} {todo'} pty parg pats pmaps pid rhs
          ((DelayGroup {tyarg} {valarg} ((MkPatClause pvars pmaps' ps tid tm) :: rest)) :: gs)
                 | (DelayMatch {tyarg} {valarg})
         = do let l = mkSizeOf [tyarg, valarg]
              let newps = newPats [(top, pty), (top, parg)] (ConsMatch (ConsMatch NilMatch)) ps
              let pats' = updatePatNames (updateNames [(valarg, parg), (tyarg, pty)])
                                         (weakensN l pats)
              let newclause : PatClause (tyarg :: valarg :: todo')
                                        (vars' :< tyarg :< valarg)
                    = MkPatClause pvars (weakensN l pmaps) (newps ++ pats') pid
                                        (weakensN l rhs)
              pure ((DelayGroup (MkPatClause pvars pmaps' ps tid tm :: rest ++ [newclause]))
                         :: gs)
      addDelayG pty parg pats pmaps pid rhs (g :: gs) | NoMatch
         = do gs' <- addDelayG pty parg pats pmaps pid rhs gs
              pure (g :: gs')

    addConstG : {vars', todo' : _} ->
                Constant -> NamedPats todo' vars' ->
                PMappings vars' -> Int -> (rhs : Term vars') ->
                (acc : List (Group todo' vars')) ->
                Core (List (Group todo' vars'))
    addConstG c pats pmaps pid rhs []
        = pure [ConstGroup c [MkPatClause pvars pmaps pats pid rhs]]
    addConstG {todo'} {vars'} c pats pmaps pid rhs (g :: gs) with (checkGroupMatch (CConst c) [] g)
      addConstG {todo'} {vars'} c pats pmaps pid rhs
              ((ConstGroup c ((MkPatClause pvars pmaps' ps tid tm) :: rest)) :: gs) | ConstMatch
          = let newclause : PatClause todo' vars'
                  = MkPatClause pvars pmaps pats pid rhs in
                pure ((ConstGroup c
                      (MkPatClause pvars pmaps' ps tid tm :: rest ++ [newclause])) :: gs)
      addConstG c pats pmaps pid rhs (g :: gs) | NoMatch
          = do gs' <- addConstG c pats pmaps pid rhs gs
               pure (g :: gs')

    addGroup : {vars, todo, idx : _} ->
               RigCount -> Pat -> (0 p : IsVar nm idx vars) ->
               NamedPats todo vars ->
               PMappings vars -> Int -> Term vars ->
               List (Group todo vars) ->
               Core (List (Group todo vars))
    -- In 'As' replace the name on the RHS with a reference to the
    -- variable we're doing the case split on
    addGroup rig (PAs fc n p) pprf pats pmaps pid rhs acc
         = addGroup rig p pprf pats pmaps pid (substName zero n (Local fc (Just True) _ pprf) rhs) acc
    addGroup rig (PCon cfc n t a pargs) pprf pats pmaps pid rhs acc
         = if a == length pargs
              then addConG rig n t (cast pargs) pats pmaps pid rhs acc
              else throw (CaseCompile cfc fn (NotFullyApplied n))
    addGroup rig (PTyCon cfc n a pargs) pprf pats pmaps pid rhs acc
         = if a == length pargs
           then addConG rig n 0 (cast pargs) pats pmaps pid rhs acc
           else throw (CaseCompile cfc fn (NotFullyApplied n))
    addGroup rig (PArrow _ _ s t) pprf pats pmaps pid rhs acc
         = addConG rig (UN $ Basic "->") 0 [(top, s), (top, t)] pats pmaps pid rhs acc
    -- Go inside the delay; we'll flag the case as needing to force its
    -- scrutinee (need to check in 'caseGroups below)
    addGroup _ (PDelay _ _ pty parg) pprf pats pmaps pid rhs acc
         = addDelayG pty parg pats pmaps pid rhs acc
    addGroup _ (PConst _ c) pprf pats pmaps pid rhs acc
         = addConstG c pats pmaps pid rhs acc
    addGroup _ _ pprf pats pmaps pid rhs acc = pure acc -- Can't happen, not a constructor
           -- FIXME: Is this possible to rule out with a type? Probably.

    gc : {a, vars, todo : _} ->
         List (Group todo vars) ->
         List (PatClause (a :: todo) vars) ->
         Core (List (Group todo vars))
    gc acc [] = pure acc
    gc {a} acc ((MkPatClause _ pmaps (MkInfo c pat pprf _ :: pats) pid rhs) :: cs)
        = do acc' <- addGroup c pat pprf pats pmaps pid rhs acc
             gc acc' cs

getFirstPat : NamedPats (p :: ps) ns -> Pat
getFirstPat (p :: _) = pat p

getFirstArgType : NamedPats (p :: ps) ns -> ArgType ns
getFirstArgType (p :: _) = argType p

||| Store scores alongside rows of named patterns. These scores are used to determine
||| which column of patterns to switch on first. One score per column.
data ScoredPats : List Name -> Scoped where
     Scored : List (NamedPats (p :: ps) ns) -> Vect (length (p :: ps)) Int -> ScoredPats (p :: ps) ns

{ps : _} -> Show (ScoredPats ps ns) where
  show (Scored xs ys) = (show ps) ++ "//" ++ (show ys)

zeroedScore : {ps : _} -> List (NamedPats (p :: ps) ns) -> ScoredPats (p :: ps) ns
zeroedScore nps = Scored nps (replicate (S $ length ps) 0)

||| Proof that a value `v` inserted in the middle of a list with
||| prefix `ps` and suffix `qs` can equivalently be snoced with
||| `ps` or consed with `qs` before appending `qs` to `ps`.
elemInsertedMiddle : (v : a) -> (ps,qs : List a) -> (ps ++ (v :: qs)) = ((ps `snoc` v) ++ qs)
elemInsertedMiddle v [] qs = Refl
elemInsertedMiddle v (x :: xs) qs = rewrite elemInsertedMiddle v xs qs in Refl

||| Helper to find a single highest scoring name (or none at all) while
||| retaining the context of all names processed.
highScore : {prev : List Name} ->
            (names : List Name) ->
            (scores : Vect (length names) Int) ->
            (highVal : Int) ->
            (highIdx : (n ** NVarL n (prev ++ names))) ->
            (duped : Bool) ->
            Maybe (n ** NVarL n (prev ++ names))
highScore [] [] high idx True = Nothing
highScore [] [] high idx False = Just idx
highScore (x :: xs) (y :: ys) high idx duped =
  let next = highScore {prev = prev `snoc` x} xs ys
      prf = elemInsertedMiddle x prev xs
  in  rewrite prf in
        case compare y high of
             LT => next high (rewrite sym $ prf in idx) duped
             EQ => next high (rewrite sym $ prf in idx) True
             GT => next y (x ** rewrite sym $ prf in weakenNVarL (mkSizeOf prev) (MkNVarL First)) False

||| Get the index of the highest scoring column if there is one.
||| If no column has a higher score than all other columns then
||| the result is Nothing indicating we need to apply more scoring
||| to break the tie.
||| Suggested heuristic application order: f, b, a.
highScoreIdx : {p : _} -> {ps : _} -> ScoredPats (p :: ps) ns -> Maybe (n ** NVarL n (p :: ps))
highScoreIdx (Scored xs (y :: ys)) = highScore {prev = []} (p :: ps) (y :: ys) (y - 1) (p ** MkNVarL First) False

||| Apply the penalty function to the head constructor's
||| arity. Produces 0 for all non-head-constructors.
headConsPenalty : (penality : Nat -> Int) -> Pat -> Int
headConsPenalty p (PAs _ _ w)        = headConsPenalty p w
headConsPenalty p (PCon _ n _ arity pats) = p arity
headConsPenalty p (PTyCon _ _ arity _)    = p arity
headConsPenalty _ (PConst _ _)       = 0
headConsPenalty _ (PArrow _ _ _ _)   = 0
headConsPenalty p (PDelay _ _ _ w)   = headConsPenalty p w
headConsPenalty _ (PLoc _ _)         = 0
headConsPenalty _ (PUnmatchable _ _) = 0

||| Apply the given function that scores a pattern to all patterns and then
||| sum up the column scores and add to the ScoredPats passed in.
consScoreHeuristic : {ps : _} -> (scorePat : Pat -> Int) -> ScoredPats ps ns -> ScoredPats ps ns
consScoreHeuristic _ sps@(Scored [] _) = sps -- can't update scores without any patterns
consScoreHeuristic scorePat (Scored xs ys) =
  let columnScores = sum <$> scoreColumns xs
      ys' = zipWith (+) ys columnScores
  in  Scored xs ys'
  where
    -- also returns NamePats of remaining columns while its in there
    -- scoring the first column.
    scoreFirstColumn : (nps : List (NamedPats (p' :: ps') ns)) ->
                       (res : List (NamedPats ps' ns) ** (LengthMatch nps res, Vect (length nps) Int))
    scoreFirstColumn [] = ([] ** (NilMatch, []))
    scoreFirstColumn ((w :: ws) :: nps) =
      let (ws' ** (prf, scores)) = scoreFirstColumn nps
      in  (ws :: ws' ** (ConsMatch prf, scorePat (pat w) :: scores))

    scoreColumns : {ps' : _} -> (nps : List (NamedPats ps' ns)) -> Vect (length ps') (Vect (length nps) Int)
    scoreColumns {ps' = []} nps = []
    scoreColumns {ps' = (w :: ws)} nps =
      let (rest ** (prf, firstColScore)) = scoreFirstColumn nps
      in  firstColScore :: (rewrite lengthsMatch prf in scoreColumns rest)

||| Add 1 to each non-default pat in the first row.
||| This favors constructive matching first and reduces tree depth on average.
heuristicF : {ps : _} -> ScoredPats (p :: ps) ns -> ScoredPats (p :: ps) ns
heuristicF sps@(Scored [] _) = sps
heuristicF (Scored (x :: xs) ys) =
  let columnScores = scores x
      ys' = zipWith (+) ys columnScores
  in  Scored (x :: xs) ys'
  where
    isBlank : Pat -> Bool
    isBlank (PLoc _ _) = True
    isBlank _ = False

    scores : NamedPats ps' ns' -> Vect (length ps') Int
    scores [] = []
    scores (y :: ys) = let score : Int = if isBlank (pat y) then 0 else 1
                       in  score :: scores ys

||| Subtract 1 from each column for each pat that represents a head constructor.
||| This favors pats that produce less branching.
heuristicB : {ps : _} -> ScoredPats ps ns -> ScoredPats ps ns
heuristicB = consScoreHeuristic (headConsPenalty (\arity => if arity == 0 then 0 else -1))

||| Subtract the sum of the arities of constructors in each column.
heuristicA : {ps : _} -> ScoredPats ps ns -> ScoredPats ps ns
heuristicA = consScoreHeuristic (headConsPenalty (negate . cast))

applyHeuristics : {p : _} ->
                  {ps : _} ->
                  ScoredPats (p :: ps) ns ->
                  List (ScoredPats (p :: ps) ns -> ScoredPats (p :: ps) ns) ->
                  Maybe (n ** NVarL n (p :: ps))
applyHeuristics x [] = highScoreIdx x
applyHeuristics x (f :: fs) = highScoreIdx x <|> applyHeuristics (f x) fs

||| Based only on the heuristic-score of columns, get the index of
||| the column that should be processed next.
|||
||| The scoring is inspired by results from the paper:
||| http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf
nextIdxByScore : {p : _} ->
                 {ps : _} ->
                 (useHeuristics : Bool) ->
                 Phase ->
                 List (NamedPats (p :: ps) ns) ->
                 (n ** NVarL n (p :: ps))
nextIdxByScore False _ _            = (_ ** (MkNVarL First))
nextIdxByScore _ (CompileTime _) _  = (_ ** (MkNVarL First))
nextIdxByScore True RunTime xs      =
  fromMaybe (_ ** (MkNVarL First)) $
    applyHeuristics (zeroedScore xs) [heuristicF, heuristicB, heuristicA]

-- Check whether all the initial patterns have the same concrete, known
-- and matchable type, which is multiplicity > 0.
-- If so, it's okay to match on it
sameType : {ns : _} ->
           {auto c : Ref Ctxt Defs} ->
           FC -> Phase -> Name ->
           Env Term ns -> List (NamedPats (p :: ps) ns) ->
           Core ()
sameType fc phase fn env [] = pure ()
sameType {ns} fc phase fn env (p :: xs)
    = do defs <- get Ctxt
         case getFirstArgType p of
              Known _ t => sameTypeAs phase
                                      !(expand !(nf env t))
                                      (map getFirstArgType xs)
              ty => throw (CaseCompile fc fn DifferingTypes)
  where
    firstPat : NamedPats (np :: nps) ns -> Pat
    firstPat (pinf :: _) = pat pinf

    headEq : NF ns -> NF ns -> Phase -> Bool
    headEq (VBind _ _ (Pi _ _ _ _) _) (VBind _ _ (Pi _ _ _ _) _) _ = True
    headEq (VTCon _ n _ _) (VTCon _ n' _ _) _ = n == n'
    headEq (VCase _ _ _ sc _ _) (VCase _ _ _ sc' _ _) phase = headEq sc sc' phase
    headEq (VPrimVal _ c) (VPrimVal _ c') _ = c == c'
    headEq (VType _ _) (VType _ _) _ = True
    headEq (VApp _ _ n _ _) (VApp _ _ n' _ _) RunTime = n == n'
    headEq (VErased _ (Dotted x)) y ph = headEq x y ph
    headEq x (VErased _ (Dotted y)) ph = headEq x y ph
    headEq (VErased _ _) _ RunTime = True
    headEq _ (VErased _ _) RunTime = True
    headEq _ _ _ = False

    sameTypeAs : Phase -> NF ns -> List (ArgType ns) -> Core ()
    sameTypeAs _ ty [] = pure ()
    sameTypeAs ph ty (Known r t :: xs) =
         do defs <- get Ctxt
            if headEq ty !(expand !(nf env t)) phase
               then sameTypeAs ph ty xs
               else throw (CaseCompile fc fn DifferingTypes)
    sameTypeAs p ty _ = throw (CaseCompile fc fn DifferingTypes)

-- Check whether all the initial patterns are the same, or are all a variable.
-- If so, we'll match it to refine later types and move on
samePat : List (NamedPats (p :: ps) ns) -> Bool
samePat [] = True
samePat (pi :: xs)
    = samePatAs (dropAs (getFirstPat pi))
                (map (dropAs . getFirstPat) xs)
  where
    dropAs : Pat -> Pat
    dropAs (PAs _ _ p) = p
    dropAs p = p

    samePatAs : Pat -> List Pat -> Bool
    samePatAs p [] = True
    samePatAs (PTyCon fc n a args) (PTyCon _ n' _ _ :: ps)
        = n == n' && samePatAs (PTyCon fc n a args) ps
    samePatAs (PCon fc n t a args) (PCon _ n' t' _ _ :: ps)
        = n == n' && t == t' && samePatAs (PCon fc n t a args) ps
    samePatAs (PConst fc c) (PConst _ c' :: ps)
        = c == c' && samePatAs (PConst fc c) ps
    samePatAs (PArrow fc x s t) (PArrow _ _ s' t' :: ps)
        = samePatAs (PArrow fc x s t) ps
    samePatAs (PDelay fc r t p) (PDelay _ _ _ _ :: ps)
        = samePatAs (PDelay fc r t p) ps
    samePatAs (PLoc fc n) (PLoc _ _ :: ps) = samePatAs (PLoc fc n) ps
    samePatAs x y = False

getFirstCon : NamedPats (p :: ps) ns -> Pat
getFirstCon (p :: _) = pat p

-- Count the number of distinct constructors in the initial pattern
countDiff : List (NamedPats (p :: ps) ns) -> Nat
countDiff xs = length (distinct [] (map getFirstCon xs))
  where
    isVar : Pat -> Bool
    isVar (PAs _ _ p) = isVar p
    isVar (PCon _ _ _ _ _) = False
    isVar (PTyCon _ _ _ _) = False
    isVar (PConst _ _) = False
    isVar (PArrow _ _ _ _) = False
    isVar (PDelay _ _ _ p) = False
    isVar _ = True

    -- Return whether two patterns would lead to the same match
    sameCase : Pat -> Pat -> Bool
    sameCase (PAs _ _ p) p' = sameCase p p'
    sameCase p (PAs _ _ p') = sameCase p p'
    sameCase (PCon _ _ t _ _) (PCon _ _ t' _ _) = t == t'
    sameCase (PTyCon _ t _ _) (PTyCon _ t' _ _) = t == t'
    sameCase (PConst _ c) (PConst _ c') = c == c'
    sameCase (PArrow _ _ _ _) (PArrow _ _ _ _) = True
    sameCase (PDelay _ _ _ _) (PDelay _ _ _ _) = True
    sameCase x y = isVar x && isVar y

    distinct : List Pat -> List Pat -> List Pat
    distinct acc [] = acc
    distinct acc (p :: ps)
       = if elemBy sameCase p acc
            then distinct acc ps
            else distinct (p :: acc) ps

getScore : {ns : _} ->
           {auto c : Ref Ctxt Defs} ->
           FC -> Phase -> Name ->
           List (NamedPats (p :: ps) ns) ->
           Core (Either CaseError ())
getScore fc phase name npss
    = do catch (do sameType fc phase name (mkEnv fc ns) npss
                   pure (Right ()))
               $ \case
                 CaseCompile _ _ err => pure $ Left err
                 err => throw err

||| Pick the leftmost matchable thing with all constructors in the
||| same family, or all variables, or all the same type constructor.
pickNextViable : {p, ns, ps : _} ->
           {auto c : Ref Ctxt Defs} ->
           FC -> Phase -> Name -> List (NamedPats (p :: ps) ns) ->
           Core (n ** NVarL n (p :: ps))
-- last possible variable
pickNextViable {ps = []} fc phase fn npss
    = if samePat npss
         then pure (_ ** MkNVarL First)
         else do Right () <- getScore fc phase fn npss
                       | Left err => throw (CaseCompile fc fn err)
                 pure (_ ** MkNVarL First)
pickNextViable {ps = q :: qs} fc phase fn npss
    = if samePat npss
         then pure (_ ** MkNVarL First)
         else  case !(getScore fc phase fn npss) of
                    Right () => pure (_ ** MkNVarL First)
                    _ => do (_ ** MkNVarL var) <- pickNextViable fc phase fn (map tail npss)
                            pure (_ ** MkNVarL (Later var))

moveFirst : {idx : Nat} -> (0 el : IsVarL nm idx ps) -> NamedPats ps ns ->
            NamedPats (nm :: dropIsVarL ps el) ns
moveFirst el nps = getPat el nps :: dropPat el nps

shuffleVars : {idx : Nat} -> (0 el : IsVarL nm idx todo) -> PatClause todo vars ->
              PatClause (nm :: dropIsVarL todo el) vars
shuffleVars First orig@(MkPatClause pvars pmaps lhs pid rhs) = orig -- no-op
shuffleVars el (MkPatClause pvars pmaps lhs pid rhs)
    = MkPatClause pvars pmaps (moveFirst el lhs) pid rhs

addForced : {vars : _} -> Var vars -> Pat -> PMappings vars -> PMappings vars
addForced n p pmaps
    = { pforced $= ((n, mkTerm vars (pvars pmaps) p) ::) } pmaps
  where
    mkTerm : (vars : SnocList Name) -> List (Name, Var vars) -> Pat -> Term vars
    mkTerm vars ps (PAs fc x y) = mkTerm vars ps y
    mkTerm vars ps (PCon fc x tag arity xs)
        = applySpine fc (Ref fc (DataCon tag arity) x)
                   (map (\ (c, t) => (c, mkTerm vars ps t)) xs)
    mkTerm vars ps (PTyCon fc x arity xs)
        = applySpine fc (Ref fc (TyCon arity) x)
                   (map (\ (c, t) => (c, mkTerm vars ps t)) xs)
    mkTerm vars ps (PConst fc c) = PrimVal fc c
    mkTerm vars ps (PArrow fc x s t)
        = Bind fc x (Pi fc top Explicit (mkTerm vars ps s))
                    (mkTerm (vars :< x) (map (\ (n, tm) => (n, weaken tm)) ps) t)
    mkTerm vars ps (PDelay fc r ty p)
        = TDelay fc r (mkTerm vars ps ty) (mkTerm vars ps p)
    mkTerm vars ps (PLoc fc n)
        = case isVar n vars of
               Just (MkVar prf) => Local fc Nothing _ prf
               _ => case lookup n ps of
                         Nothing => Ref fc Bound n
                         Just (MkVar prf) => Local fc Nothing _ prf
    mkTerm vars ps (PUnmatchable fc tm) = embed tm

addPVarMap : FC -> Name -> Var vars -> PMappings vars -> PMappings vars
addPVarMap fc n var pmaps
    = case lookup n (pvars pmaps) of
           Nothing => { pvars $= ((n, var) ::) } pmaps
           Just (MkVar var') =>
                { pforced $= ((var, Local fc Nothing _ var') :: ) } pmaps

mutual
  {- 'PatClause' contains a list of patterns still to process (that's the
     "todo") and a right hand side with the variables we know about "vars".
     So "match" builds the remainder of the case tree for
     the unprocessed patterns. "err" is the tree for when the patterns don't
     cover the input (i.e. the "fallthrough" pattern, which at the top
     level will be an error). -}
  match : {vars, todo : _} ->
          {auto i : Ref PName Int} ->
          {auto c : Ref Ctxt Defs} ->
          FC -> Name -> Phase ->
          List (PatClause todo vars) -> (err : Maybe (CaseTree vars)) ->
          Core (CaseTree vars)
  -- Before 'partition', reorder the arguments so that the one we
  -- inspect next has a concrete type that is the same in all cases, and
  -- has the most distinct constructors (via pickNextViable)
  match {todo = (_ :: _)} fc fn phase clauses err
      = do let nps = getNPs <$> clauses
           let (_ ** (MkNVarL next)) = nextIdxByScore (caseTreeHeuristics !getSession) phase nps
           let prioritizedClauses = shuffleVars next <$> clauses
           (n ** MkNVarL next') <- pickNextViable fc phase fn (getNPs <$> prioritizedClauses)
           log "compile.casetree" 25 $ "Clauses " ++ show clauses
           log "compile.casetree" 25 $ "Err " ++ show err
           log "compile.casetree.pick" 25 $ "Picked " ++ show n ++ " as the next split"
           let clauses' = shuffleVars next' <$> prioritizedClauses
           log "compile.casetree.clauses" 25 $
             unlines ("Using clauses:" :: map (("  " ++) . show) clauses')
           let ps = partition phase clauses'
           log "compile.casetree.partition" 25 $ "Got Partition:\n" ++ show ps
           mix <- mixture fc fn phase ps err
           case mix of
             Nothing =>
               do log "compile.casetree.intermediate" 25 "match: No clauses"
                  pure (TUnmatched fc "No clauses in \{show fn}")
             Just m =>
               do log "compile.casetree.intermediate" 25 $ "match: new case tree " ++ show m
                  Core.pure m
  match {todo = []} fc fn phase [] err
       = maybe (pure (TUnmatched fc "No patterns in \{show fn}"))
               pure err
  match {todo = []} fc fn phase ((MkPatClause _ pmaps [] pid (Erased _ Impossible)) :: _) err
       = pure (TImpossible fc)
  match {todo = []} fc fn phase ((MkPatClause _ pmaps [] pid rhs) :: _) err
       = do log "compile.casetree" 5 ("PMappings at RHS: " ++ show pmaps)
            pure $ STerm pid (mapMaybe notPV (pvars pmaps) ++
                              substForced (pvars pmaps) (pforced pmaps)) rhs
    where
      -- It's also a forced equality if it appears in the 'pvars' as an
      -- equality between bound locals, but hasn't found its way into pforced
      notPV : (Name, Var vars) -> Maybe (Var vars, Term vars)
      notPV (n, var)
          = case isVar n vars of
                 Just (MkVar prf) => Just (var, Local fc Nothing _ prf)
                 _ => Nothing

  caseGroups : {pvar, vars, todo : _} ->
               {auto i : Ref PName Int} ->
               {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Phase -> RigCount ->
               {idx : Nat} -> (0 p : IsVar pvar idx vars) -> Term vars ->
               List (Group todo vars) -> Maybe (CaseTree vars) ->
               Core (CaseTree vars)
  caseGroups {vars} fc fn phase c el ty gs errorCase
      = do g <- altGroups gs
           log "compile.casetree" 50 $ "Making case with " ++ show gs
           log "compile.casetree" 50 $ "Makes " ++ show g
           pure (TCase fc c _ el (resolveNames vars ty) g)
    where
      mkScope : forall vars . (vs : SnocList Name) ->
                              (ms : SnocList RigCount) ->
                              TCaseScope (vars ++ vs) ->
                TCaseScope vars
      mkScope [<] _ rhs = rhs
      mkScope (sx :< y) (ms :< c) rhs = mkScope sx ms (TArg c y rhs)
      mkScope (sx :< y) _ rhs = mkScope sx [<] (TArg top y rhs)

      altGroups : List (Group todo vars) -> Core (List (TCaseAlt vars))
      altGroups [] = maybe (pure [])
                           (\e => pure [TDefaultCase fc e])
                           errorCase
      altGroups (ConGroup {newargs} cn tag rigs rest :: cs)
          = do crest <- match fc fn phase rest (map (weakensN (mkSizeOf newargs)) errorCase)
               cs' <- altGroups cs
               pure (TConCase fc cn tag (mkScope (cast newargs) (cast rigs) (rewrite sym $ fishAsSnocAppend vars newargs in TRHS crest)) :: cs')
      altGroups (DelayGroup {tyarg} {valarg} rest :: cs)
          = do crest <- match fc fn phase rest (map (weakenNs (mkSizeOf [<tyarg, valarg])) errorCase)
               cs' <- altGroups cs
               pure (TDelayCase fc tyarg valarg crest :: cs')
      altGroups (ConstGroup c rest :: cs)
          = do crest <- match fc fn phase rest errorCase
               cs' <- altGroups cs
               pure (TConstCase fc c crest :: cs')

  conRule : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            FC -> Name -> Phase ->
            List (PatClause (a :: todo) vars) ->
            Maybe (CaseTree vars) ->
            Core (CaseTree vars)
  conRule fc fn phase [] err = maybe (pure (TUnmatched fc "No constructor clauses in \{show fn}")) pure err
  -- ASSUMPTION, not expressed in the type, that the patterns all have
  -- the same variable (pprf) for the first argument. If not, the result
  -- will be a broken case tree... so we should find a way to express this
  -- in the type if we can.
  conRule {a} fc fn phase cs@(MkPatClause pvars pmaps (MkInfo c pat pprf fty :: pats) pid rhs :: rest) err
      = do refinedcs <- traverse (substInClause fc) cs
           log "compile.casetree" 5 $ "conRule refinedcs: " ++ show refinedcs
           groups <- groupCons fc fn pvars refinedcs
           log "compile.casetree" 5 $ "conRule groups: " ++
                    show a ++ ", " ++ show groups ++ " , " ++ show cs
           ty <- case fty of
                      Known _ t => pure t
                      Stuck tm => do logTerm "compile.casetree" 25 "Stuck" tm
                                     throw (CaseCompile fc fn UnknownType)
                      _ => do log "compile.casetree" 25 "Unknown type"
                              throw (CaseCompile fc fn UnknownType)
           -- The 'pmaps' carry on being propagated through the rest of the
           -- tree (via 'groups') so we don't use them here
           caseGroups fc fn phase c pprf ty groups err

  varRule : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            FC -> Name -> Phase ->
            List (PatClause (a :: todo) vars) ->
            Maybe (CaseTree vars) ->
            Core (CaseTree vars)
  varRule {vars} {a} fc fn phase cs err
      = do alts' <- traverse updateVar cs
           match fc fn phase alts' err
    where
      updateVar : PatClause (a :: todo) vars -> Core (PatClause todo vars)
      -- replace the name with the relevant variable on the rhs
      updateVar (MkPatClause pvars pmaps (MkInfo {idx} {name} _ (PLoc pfc n) prf fty :: pats) pid rhs)
          = do log "compile.casetree.updateVar" 50
                  "Replacing \{show n} with \{show name}[\{show idx}] in \{show rhs}"
               log "compile.casetree" 5 $ "Var update " ++
                    show a ++ ", " ++ show n ++ ", vars: " ++ show (toList vars) ++ " ==> " ++ show !(toFullNames rhs)
               let pmaps' = addPVarMap pfc n (MkVar prf) pmaps
               let rhs' = substName zero n (Local pfc (Just False) _ prf) rhs
               logTerm "compile.casetree" 5 "updateVar-2 rhs'" rhs'
               pure $ MkPatClause (n :: pvars) pmaps'
                        !(substInPats fc a (Local pfc (Just False) _ prf) pats)
                        pid (substName zero n (Local pfc (Just False) _ prf) rhs)
      -- If it's an as pattern, replace the name with the relevant variable on
      -- the rhs then continue with the inner pattern
      updateVar (MkPatClause pvars pmaps (MkInfo c (PAs pfc n pat) prf fty :: pats) pid rhs)
          = do log "compile.casetree" 5 $ "Var replace " ++
                    show a ++ ", " ++ show n ++ ", vars: " ++ show (toList vars) ++ " ==> " ++ show !(toFullNames rhs)
               pats' <- substInPats fc a (mkTerm _ pat) pats
               let rhs' = substName zero n (Local pfc (Just True) _ prf) rhs
               logTerm "compile.casetree" 5 "updateVar-3 rhs'" rhs'
               updateVar (MkPatClause pvars pmaps (MkInfo c pat prf fty :: pats') pid rhs')
      -- match anything, name won't appear in rhs but need to update
      -- LHS pattern types based on what we've learned
      updateVar (MkPatClause pvars pmaps (MkInfo _ pat prf fty :: pats) pid rhs)
          = do log "compile.casetree" 5 $ "Forced Var update " ++
                     show a ++ ", vars: " ++ show (toList vars) ++ ", " ++ show !(toFullNames pat) ++ " ==> "
                     ++ show !(toFullNames rhs)
               let pmaps' = addForced (MkVar prf) pat pmaps
               let ptm = mkTerm vars pat
               pure $ MkPatClause pvars pmaps'
                        !(substInPats fc a ptm pats) pid rhs

  mixture : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            {ps : List (PatClause (a :: todo) vars)} ->
            FC -> Name -> Phase ->
            Partitions ps ->
            Maybe (CaseTree vars) ->
            Core (Maybe (CaseTree vars))
  mixture fc fn phase (ConClauses cs rest) err
      = do log "compile.casetree" 25 $ "Mixture ConClauses Rest: " ++ show rest ++ ", cs: " ++ show cs
           fallthrough <- mixture fc fn phase rest err
           pure (Just !(conRule fc fn phase cs fallthrough))
  mixture fc fn phase (VarClauses vs rest) err
      = do log "compile.casetree" 25 $ "Mixture VarClauses Rest: " ++ show rest ++ ", vs: " ++ show vs
           fallthrough <- mixture fc fn phase rest err
           pure (Just !(varRule fc fn phase vs fallthrough))
  mixture fc fn {a} {todo} phase NoClauses err
      = pure err

export
mkPat : {auto c : Ref Ctxt Defs} ->
        (matchable : Bool) -> List (RigCount, Pat) -> ClosedTerm -> ClosedTerm -> Core Pat
mkPat _ [] orig (Ref fc Bound n) = pure $ PLoc fc n
mkPat True args orig (Ref fc (DataCon t a) n) = pure $ PCon fc n t a (cast args)
mkPat True args orig (Ref fc (TyCon a) n) = pure $ PTyCon fc n a (cast args)
mkPat True args orig (Ref fc Func n)
  = do prims <- getPrimitiveNames
       mtm <- normalisePrims (const True) isPConst True prims n (cast $ map snd args) orig Env.empty
       case mtm of
         Just tm => if tm /= orig -- check we made progress; if there's an
                                  -- unresolved interface, we might be stuck
                                  -- and we'd loop forever
                       then mkPat True [] tm tm
                       else -- Possibly this should be an error instead?
                            pure $ PUnmatchable (getLoc orig) orig
         Nothing =>
           do log "compile.casetree" 10 $
                "Unmatchable function: " ++ show n
              pure $ PUnmatchable (getLoc orig) orig
mkPat True args orig (Bind fc x (Pi _ _ _ s) t)
    -- For (b:Nat) -> b, the codomain looks like b [__], but we want `b` as the pattern
    = case subst (Erased fc Placeholder) t of
        App _ t'@(Ref fc Bound n) _ (Erased {}) => pure $ PArrow fc x !(mkPat True [] s s) !(mkPat False [] t' t')
        t' => pure $ PArrow fc x !(mkPat True [] s s) !(mkPat False [] t' t')
mkPat True args orig (App fc fn c@_ arg)
    = do parg <- mkPat True [] arg arg
         mkPat True ((c, parg) :: args) orig fn
-- Assumption is that clauses are converted to explicit names
mkPat True args orig (As fc _ (Ref _ Bound n) ptm)
    = pure $ PAs fc n !(mkPat True [] ptm ptm)
mkPat True args orig (As fc _ _ ptm)
    = mkPat True [] orig ptm
mkPat True args orig (TDelay fc r ty p)
    = pure $ PDelay fc r !(mkPat True [] orig ty) !(mkPat True [] orig p)
mkPat True args orig (PrimVal fc $ PrT c) -- Primitive type constant
    = pure $ PTyCon fc (UN (Basic $ show c)) 0 [<]
mkPat True args orig (PrimVal fc c) = pure $ PConst fc c -- Non-type constant
mkPat True args orig (TType fc _) = pure $ PTyCon fc (UN $ Basic "Type") 0 [<]
mkPat _ args orig tm
   = do log "compile.casetree" 10 $
          "Catchall: marking " ++ show tm ++ " as unmatchable"
        pure $ PUnmatchable (getLoc orig) orig

export
argToPat : {auto c : Ref Ctxt Defs} -> (RigCount, ClosedTerm) -> Core (RigCount, Pat)
argToPat = traversePair $ \tm => mkPat True [] tm tm

mkPatClause : {auto c : Ref Ctxt Defs} ->
              FC -> Name ->
              (args : List Name) -> SizeOf args -> ClosedTerm ->
              Int -> (List (RigCount, Pat), ClosedTerm) ->
              Core (PatClause args (cast args))
mkPatClause fc fn args s ty pid (ps, rhs)
    = maybe (throw (CaseCompile fc fn DifferingArgNumbers))
            (\eq =>
               do defs <- get Ctxt
                  logTerm "compile.casetree" 20 "mkPatClause ty" ty
                  nty <- expand !(nf Env.empty ty)
                  logNF "compile.casetree" 20 "mkPatClause nty: " Env.empty nty
                  -- The arguments are in reverse order, so we need to
                  -- read what we know off 'nty', and reverse it
                  argTys <- getArgTys Env.empty args nty
                  log "compile.casetree" 20 $ "mkPatClause args: " ++ show args ++ ", argTys: " ++ show argTys
                  ns <- logQuiet $ mkNames args ps eq s.hasLength argTys
                  log "compile.casetree" 20 $
                    "Make pat clause for names " ++ show ns
                     ++ " in LHS " ++ show ps
                  pure (MkPatClause [] initPMap ns pid (weakensN s rhs)))
            (checkLengthMatch args ps)
  where
    mkNames : (vars : List Name) -> (ps : List (RigCount, Pat)) ->
              (0 _ : LengthMatch vars ps) ->
              {n : _} -> (0 _ : HasLength n vars) ->
              List (ArgType [<]) ->
              Core (NamedPats vars (cast vars))
    mkNames [] [] NilMatch _ _ = pure []
    mkNames (r :: args) ((c, p) :: ps) (ConsMatch eq) (S h) as
      = do let (ty, as) : (ArgType ([<r] <>< args), List (ArgType [<]))
               := case as of
                      [] => (Unknown, [])
                      (a :: as) => (embed a, as)
           let info = MkInfo {name=r} c p (isVarFishily {outer=[<]} h) ty
           rest <- mkNames args ps eq h as
           pure (info :: rewrite fishAsSnocAppend [<r] args in embed rest)

export
patCompile : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Phase ->
             ClosedTerm -> List (List (RigCount, Pat), ClosedTerm) ->
             Maybe (CaseTree Scope.empty) ->
             Core (args ** CaseTree args)
patCompile fc fn phase ty [] def
    = maybe (pure (Scope.empty ** TUnmatched fc "\{show fn} not defined"))
            (\e => pure (Scope.empty ** e))
            def
patCompile fc fn phase ty (p :: ps) def
    = do let ns = getNames 0 (fst p)
         log "compile.casetree" 25 $ "ns: " ++ show ns
         pats <- mkPatClausesFrom 0 ns (mkSizeOf ns) (p :: ps)
         -- low verbosity level: pretty print fully resolved names
         logC "compile.casetree" 5 $ do
           pats <- traverse toFullNames pats
           pure $ "Pattern clauses:\n"
                ++ show (indent 2 $ vcat $ pretty <$> pats)
         log "compile.casetree" 25 $ "Def " ++ show def
         -- higher verbosity: dump the raw data structure
         log "compile.casetree" 10 $ "pats " ++ show pats
         i <- newRef PName (the Int 0)
         cases <- match fc fn phase pats (embed @{MaybeFreelyEmbeddable} def)
         pure (_ ** cases)
  where
    mkPatClausesFrom : Int -> (args : List Name) -> SizeOf args ->
                       List (List (RigCount, Pat), ClosedTerm) ->
                       Core (List (PatClause args (cast args)))
    mkPatClausesFrom _ _ _ [] = pure []
    mkPatClausesFrom i ns s (p :: ps)
        = do p' <- mkPatClause fc fn ns s ty i p
             ps' <- mkPatClausesFrom (i + 1) ns s ps
             pure (p' :: ps')

    getNames : Int -> List (RigCount, Pat) -> List Name
    getNames i [] = []
    getNames i (_ :: xs) = MN "arg" i :: getNames (i + 1) xs

toPatClause : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> (ClosedTerm, ClosedTerm) ->
              Core (List (RigCount, Pat), ClosedTerm)
toPatClause fc n (lhs, rhs)
    = case getFnArgsWithCounts lhs of
           (Ref ffc Func fn, args)
              => do defs <- get Ctxt
                    (np, _) <- getPosition n (gamma defs)
                    (fnp, _) <- getPosition fn (gamma defs)
                    if np == fnp
                       then do pats <- traverse argToPat args
                               log "compile.casetree" 10 $ "toPatClause args: " ++ show args ++ ", pats: " ++ show pats
                               pure (pats, rhs)
                       else throw (GenericMsg ffc ("Wrong function name in pattern LHS " ++ show (n, fn)))
           (f, args) => throw (GenericMsg fc "Not a function name in pattern LHS")

-- Assumption (given 'ClosedTerm') is that the pattern variables are
-- explicitly named. We'll assign de Bruijn indices when we're done, and
-- the names of the top level variables we created are returned in 'args'
export
simpleCase : {auto c : Ref Ctxt Defs} ->
             FC -> Phase -> Name -> ClosedTerm -> (def : Maybe (CaseTree Scope.empty)) ->
             (clauses : List (ClosedTerm, ClosedTerm)) ->
             Core (args ** CaseTree args)
simpleCase fc phase fn ty def clauses
    = do logC "compile.casetree" 5 $
                do cs <- traverse (\ (c,d) => [| MkPair (toFullNames c) (toFullNames d) |]) clauses
                   pure $ "simpleCase: Clauses:\n" ++ show (
                     indent 2 $ vcat $ flip map cs $ \ lrhs =>
                       byShow (fst lrhs) <++> pretty "=" <++> byShow (snd lrhs))
         ps <- traverse (toPatClause fc fn) clauses
         defs <- get Ctxt
         log "compile.casetree" 5 $ "ps: " ++ show ps
         patCompile fc fn phase ty ps def

mutual
  findReachedAlts : TCaseAlt ns' -> List Int
  findReachedAlts (TConCase _ _ _ t) = findReachedCaseScope t
  findReachedAlts (TDelayCase _ _ _ t) = findReached t
  findReachedAlts (TConstCase _ _ t) = findReached t
  findReachedAlts (TDefaultCase _ t) = findReached t

  findReachedCaseScope : TCaseScope a -> List Int
  findReachedCaseScope (TRHS tm) = findReached tm
  findReachedCaseScope (TArg _ _ cs) = findReachedCaseScope cs

  findReached : CaseTree ns -> List Int
  findReached (TCase _ _ _ _ _ alts) = concatMap findReachedAlts alts
  findReached (STerm i _ _) = [i]
  findReached _ = []

-- Replace a default case with explicit branches for the constructors.
-- This is easier than checking whether a default is needed when traversing
-- the tree (just one constructor lookup up front).
-- Unreachable defaults are those that when replaced by all possible constructors
-- followed by a removal of duplicate cases there is one _fewer_ total case alts.
identifyUnreachableDefaults : {auto c : Ref Ctxt Defs} ->
                              {vars : _} ->
                              FC -> Defs -> NF vars -> List (TCaseAlt vars) ->
                              Core (SortedSet Int)
-- Leave it alone if it's a primitive type though, since we need the catch
-- all case there
identifyUnreachableDefaults fc defs (VPrimVal _ _) cs = pure empty
identifyUnreachableDefaults fc defs (VType _ _) cs = pure empty
identifyUnreachableDefaults fc defs nfty cs
    = do cs' <- traverse rep cs
         let (cs'', extraClauseIdxs) = dropRep (concat cs') empty
         let extraClauseIdxs' =
           if (length cs == (length cs'' + 1))
              then extraClauseIdxs
              else empty
         -- if a clause is unreachable under all the branches it can be found under
         -- then it is entirely unreachable.
         when (not $ null extraClauseIdxs') $
           log "compile.casetree.clauses" 25 $
             "Marking the following clause indices as unreachable under the current branch of the tree: " ++ (show extraClauseIdxs')
         pure extraClauseIdxs'
  where
    rep : TCaseAlt vars -> Core (List (TCaseAlt vars))
    rep (TDefaultCase _ sc)
        = do allCons <- getCons defs nfty
             pure (map (mkAlt fc sc) allCons)
    rep c = pure [c]

    dropRep : List (TCaseAlt vars) -> SortedSet Int -> (List (TCaseAlt vars), SortedSet Int)
    dropRep [] extra = ([], extra)
    dropRep (c@(TConCase _ n t sc) :: rest) extra
          -- assumption is that there's no defaultcase in 'rest' because
          -- we've just removed it
        = let (filteredClauses, extraCases) = partition (not . tagIs t) rest
              extraClauses = extraCases >>= findReachedAlts
              (rest', extra') = dropRep filteredClauses $ fromList extraClauses
          in  (c :: rest', extra `union` extra')
    dropRep (c :: rest) extra
        = let (rest', extra') = dropRep rest extra
          in  (c :: rest', extra')

||| Find unreachable default paths through the tree for each clause.
||| This is accomplished by expanding default clases into all concrete constructions
||| and then listing the clauses reached.
||| This list of clauses can be substracted from the list of "reachable" clauses
||| and if it turns out that the number of unreachable ways to use a clause is equal
||| to the number of ways to reach a RHS for that clause then the clause is totally
||| superfluous (it will never be reached).
findExtraDefaults : {auto c : Ref Ctxt Defs} ->
                    {vars : _} ->
                    Defs -> CaseTree vars ->
                    Core (List Int)
findExtraDefaults defs ctree@(TCase fc _ idx el ty altsIn)
  = do let fenv = mkEnv fc _
       nfty <- expand !(nf fenv ty)
       extraCases <- identifyUnreachableDefaults fc defs nfty altsIn
       extraCases' <- concat <$> traverse findExtraAlts altsIn
       pure (Prelude.toList extraCases ++ extraCases')
  where
    findExtraAltsScope : {vars : _} -> TCaseScope vars -> Core (List Int)
    findExtraAltsScope (TRHS tm) = findExtraDefaults defs tm
    findExtraAltsScope (TArg c x sc) = findExtraAltsScope sc

    findExtraAlts : TCaseAlt vars -> Core (List Int)
    findExtraAlts (TConCase _ x tag ctree') = findExtraAltsScope ctree'
    findExtraAlts (TDelayCase _ x arg ctree') = findExtraDefaults defs ctree'
    findExtraAlts (TConstCase _ x ctree') = findExtraDefaults defs ctree'
    -- already handled defaults by elaborating them to all possible cons
    findExtraAlts (TDefaultCase _ ctree') = pure []

findExtraDefaults defs ctree = pure []

-- Returns the case tree under the yet-to-be-bound lambdas,
-- and a list of the clauses that aren't reachable
makePMDef : {auto c : Ref Ctxt Defs} ->
            FC -> CaseType -> Phase -> Name -> ClosedTerm -> List Clause ->
            Core (args ** (Term args, List Clause))
-- If there's no clauses, make a definition with the right number of arguments
-- for the type, which we can use in coverage checking to ensure that one of
-- the arguments has an empty type
makePMDef fc ct phase fn ty []
    = do log "compile.casetree.getpmdef" 20 "getPMDef: No clauses!"
         defs <- get Ctxt
         pure (!(getArgs 0 !(expand !(nf Env.empty ty))) ** (Unmatched fc "No clauses", []))
  where
    getArgs : Int -> ClosedNF -> Core (SnocList Name)
    getArgs i (VBind fc x (Pi _ _ _ _) sc)
        = do defs <- get Ctxt
             sc' <- expand !(sc (pure (VErased fc Placeholder)))
             pure (!(getArgs i sc') :< MN "arg" i)
    getArgs i _ = pure [<]
makePMDef fc ct phase fn ty clauses
    = do let cs = map toClosed (labelPat 0 clauses)
         (args' ** t) <- simpleCase fc phase fn ty Nothing cs
         let treeTm = mkTerm ct t
         logC "compile.casetree.getpmdef" 20 $
           do t <- toFullNames treeTm
              pure $ "Compiled to: " ++ show t ++ "\nWith " ++ show args'
         let allRHS = findReached t
         log "compile.casetree.clauses" 25 $
           "All RHSes: " ++ (show allRHS)
         defs <- get Ctxt
         extraDefaults <- findExtraDefaults defs t
         log "compile.casetree.clauses" 25 $
           "Extra defaults: " ++ (show extraDefaults)
         let unreachable = getUnreachable 0 (allRHS \\ extraDefaults) clauses
         pure (_ ** (treeTm, unreachable))
  where
    getUnreachable : Int -> List Int -> List Clause -> List Clause
    getUnreachable i is [] = []
    getUnreachable i is (c :: cs)
        = if i `elem` is
             then getUnreachable (i + 1) is cs
             else c :: getUnreachable (i + 1) is cs

    labelPat : Int -> List a -> List (String, a)
    labelPat i [] = []
    labelPat i (x :: xs) = ("pat" ++ show i ++ ":", x) :: labelPat (i + 1) xs

    mkSubstEnv : Int -> String -> Env Term vars -> SubstEnv vars [<]
    mkSubstEnv i pname [<] = Lin
    mkSubstEnv i pname (vs :< v)
        = mkSubstEnv (i + 1) pname vs :< Ref fc Bound (MN pname i)

    close : {vars : _} ->
            Env Term vars -> String -> Term vars -> ClosedTerm
    close {vars} env pname tm
        = substs (mkSizeOf vars) (mkSubstEnv 0 pname env)
                                 (rewrite appendLinLeftNeutral vars in tm)

    toClosed :  (String, Clause) -> (ClosedTerm, ClosedTerm)
    toClosed  (pname, MkClause env lhs rhs)
        = (close env pname lhs, close env pname rhs)

-- Returns the case tree, and a list of the clauses that aren't reachable
export
getPMDef : {auto c : Ref Ctxt Defs} ->
           FC -> CaseType -> Phase -> Name -> ClosedTerm -> List Clause ->
           Core (ClosedTerm, List Clause)
getPMDef fc ct p n ty cs
    = do (args ** (tree, missing)) <- makePMDef fc ct p n ty cs
         -- We need to bind lambdas, and we can only do that if we know
         -- the types of the function arguments, so normalise the type just
         -- enough to get that
--       Commented in Yaffle for performance:
--       https://github.com/edwinb/Yaffle/commit/f660b94a66da385ae6f3568998473a12a4cd769d
--          nty <- normaliseBinders [<] ty
--          let (tyargs ** env) = mkEnv [<] nty
--          let Just lenOK = areVarsCompatible args tyargs
         let tm = bindLams _ tree
--              | Nothing => throw (CaseCompile fc n CantResolveType)
         pure (tm, missing)
   where
     mkEnv : {vars : _} -> Env Term vars -> Term vars ->
             (args ** Env Term args)
     mkEnv env (Bind _ x b@(Pi pfc c p ty) sc) = mkEnv (env :< b) sc
     mkEnv env tm = (_ ** env)

     bindLams : (args' : _) ->
                Term args' -> Term [<]
     bindLams [<] tree = tree
     bindLams (as :< a) tree
         = bindLams as (Bind fc _
                           (Lam fc top
                                Explicit
                                (Erased fc Placeholder)) tree)
