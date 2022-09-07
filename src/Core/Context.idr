module Core.Context

import        Core.Case.CaseTree
import        Core.CompileExpr
import public Core.Context.Context
import public Core.Core
import        Core.Env
import        Core.Hash
import public Core.Name
import        Core.Options
import public Core.Options.Log
import public Core.TT

import Libraries.Utils.Binary
import Libraries.Utils.Scheme
import Libraries.Text.PrettyPrint.Prettyprinter

import Idris.Syntax.Pragmas

import Data.Either
import Data.Fin
import Libraries.Data.IOArray
import Libraries.Data.IntMap
import Data.List
import Data.List1
import Data.Maybe
import Data.Nat
import Libraries.Data.NameMap
import Libraries.Data.StringMap
import Libraries.Data.UserNameMap
import Libraries.Text.Distance.Levenshtein

import System.Clock
import System.Directory

%default covering

export
getContent : Context -> Ref Arr (IOArray ContextEntry)
getContent = content

export
namesResolvedAs : Context -> NameMap Name
namesResolvedAs ctxt = map Resolved ctxt.resolvedAs

-- Implemented later, once we can convert to and from full names
-- Defined in Core.TTC
export
decode : Context -> Int -> (update : Bool) -> ContextEntry -> Core GlobalDef

initSize : Int
initSize = 10000

Grow : Int
Grow = initSize

export
initCtxtS : Int -> Core Context
initCtxtS s
    = do arr <- coreLift $ newArray s
         aref <- newRef Arr arr
         pure $ MkContext
            { firstEntry = 0
            , nextEntry = 0
            , resolvedAs = empty
            , possibles = empty
            , content = aref
            , branchDepth = 0
            , staging = empty
            , visibleNS = [partialEvalNS]
            , allPublic = False
            , inlineOnly = False
            , hidden = empty
            , uconstraints = []
            }

export
initCtxt : Core Context
initCtxt = initCtxtS initSize

addPossible : Name -> Int ->
              UserNameMap (List PossibleName) -> UserNameMap (List PossibleName)
addPossible n i ps
    = case userNameRoot n of
           Nothing => ps
           Just nr =>
              case lookup nr ps of
                   Nothing => insert nr [Direct n i] ps
                   Just nis => insert nr (Direct n i :: nis) ps

addAlias : Name -> Name -> Int ->
           UserNameMap (List PossibleName) -> UserNameMap (List PossibleName)
addAlias alias full i ps
    = case userNameRoot alias of
           Nothing => ps
           Just nr =>
              case lookup nr ps of
                   Nothing => insert nr [Alias alias full i] ps
                   Just nis => insert nr (Alias alias full i :: nis) ps

export
newEntry : Name -> Context -> Core (Int, Context)
newEntry n ctxt
    = do let idx = nextEntry ctxt
         let a = content ctxt
         arr <- get Arr
         when (idx >= max arr) $
                 do arr' <- coreLift $ newArrayCopy (max arr + Grow) arr
                    put Arr arr'
         pure (idx, { nextEntry := idx + 1,
                      resolvedAs $= insert n idx,
                      possibles $= addPossible n idx
                    } ctxt)

-- Get the position of the next entry in the context array, growing the
-- array if it's out of bounds.
-- Updates the context with the mapping from name to index
export
getPosition : Name -> Context -> Core (Int, Context)
getPosition (Resolved idx) ctxt = pure (idx, ctxt)
getPosition n ctxt
    = case lookup n (resolvedAs ctxt) of
           Just idx =>
              do pure (idx, ctxt)
           Nothing => newEntry n ctxt

newAlias : Name -> Name -> Context -> Core Context
newAlias alias full ctxt
    = do (idx, ctxt) <- getPosition full ctxt
         pure $ { possibles $= addAlias alias full idx } ctxt

export
getNameID : Name -> Context -> Maybe Int
getNameID (Resolved idx) ctxt = Just idx
getNameID n ctxt = lookup n (resolvedAs ctxt)

-- Add the name to the context, or update the existing entry if it's already
-- there.
-- If we're not at the top level, add it to the staging area
export
addCtxt : Name -> GlobalDef -> Context -> Core (Int, Context)
addCtxt n val ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx (Decoded val)
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, { staging $= insert idx (Decoded val) } ctxt)

export
addEntry : Name -> ContextEntry -> Context -> Core (Int, Context)
addEntry n entry ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx entry
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, { staging $= insert idx entry } ctxt)

returnDef : Bool -> Int -> GlobalDef -> Maybe (Int, GlobalDef)
returnDef False idx def = Just (idx, def)
returnDef True idx def
    = case definition def of
           PMDef pi _ _ _ _ =>
                 if alwaysReduce pi
                    then Just (idx, def)
                    else Nothing
           _ => Nothing

export
lookupCtxtExactI : Name -> Context -> Core (Maybe (Int, GlobalDef))
lookupCtxtExactI (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just val =>
                 pure $ returnDef (inlineOnly ctxt) idx !(decode ctxt idx True val)
           Nothing =>
              do arr <- get Arr @{content ctxt}
                 Just def <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure $ returnDef (inlineOnly ctxt) idx !(decode ctxt idx True def)
lookupCtxtExactI n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupCtxtExactI (Resolved idx) ctxt

export
lookupCtxtExact : Name -> Context -> Core (Maybe GlobalDef)
lookupCtxtExact (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res =>
                do def <- decode ctxt idx True res
                   pure $ map (\(_, def) => def) $
                     returnDef (inlineOnly ctxt) idx def
           Nothing =>
              do arr <- get Arr @{content ctxt}
                 Just res <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 def <- decode ctxt idx True res
                 pure $ map (\(_, def) => def) $
                   returnDef (inlineOnly ctxt) idx def
lookupCtxtExact n ctxt
    = do Just (i, def) <- lookupCtxtExactI n ctxt
              | Nothing => pure Nothing
         pure (Just def)

export
lookupContextEntry : Name -> Context -> Core (Maybe (Int, ContextEntry))
lookupContextEntry (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res => pure (Just (idx, res))
           Nothing =>
              do let a = content ctxt
                 arr <- get Arr
                 Just res <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure (Just (idx, res))
lookupContextEntry n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupContextEntry (Resolved idx) ctxt

||| Check if the given name has been hidden by the `%hide` directive.
export
isHidden : Name -> Context -> Bool
isHidden fulln ctxt = isJust $ lookup fulln (hidden ctxt)

||| Look up a possibly hidden name in the context. The first (boolean) argument
||| controls whether names hidden by `%hide` are returned too (True=yes, False=no).
export
lookupCtxtName' : Bool -> Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupCtxtName' allowHidden n ctxt
    = case userNameRoot n of
           Nothing => do Just (i, res) <- lookupCtxtExactI n ctxt
                              | Nothing => pure []
                         pure [(n, i, res)]
           Just r =>
              do let Just ps = lookup r (possibles ctxt)
                      | Nothing => pure []
                 lookupPossibles [] ps
  where

    resn : (Name, Int, GlobalDef) -> Int
    resn (_, i, _) = i

    hlookup : Name -> NameMap () -> Maybe ()
    hlookup fulln hiddens = if allowHidden
      then Nothing
      else lookup fulln hiddens

    lookupPossibles : List (Name, Int, GlobalDef) -> -- accumulator
                      List PossibleName ->
                      Core (List (Name, Int, GlobalDef))
    lookupPossibles acc [] = pure (reverse acc)
    lookupPossibles acc (Direct fulln i :: ps)
       = case (hlookup fulln (hidden ctxt)) of
              Nothing =>
                do Just res <- lookupCtxtExact (Resolved i) ctxt
                        | Nothing => lookupPossibles acc ps
                   if matches n fulln && not (i `elem` map resn acc)
                      then lookupPossibles ((fulln, i, res) :: acc) ps
                      else lookupPossibles acc ps
              _ => lookupPossibles acc ps
    lookupPossibles acc (Alias asn fulln i :: ps)
       = case (hlookup fulln (hidden ctxt)) of
              Nothing =>
                do Just res <- lookupCtxtExact (Resolved i) ctxt
                        | Nothing => lookupPossibles acc ps
                   if (matches n asn) && not (i `elem` map resn acc)
                      then lookupPossibles ((fulln, i, res) :: acc) ps
                      else lookupPossibles acc ps
              _ => lookupPossibles acc ps

||| Look up a name in the context, ignoring names hidden by `%hide`.
export
lookupCtxtName : Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupCtxtName = lookupCtxtName' False

||| Look up a (possible hidden) name in the context.
export
lookupHiddenCtxtName : Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupHiddenCtxtName = lookupCtxtName' True

hideName : Name -> Context -> Context
hideName n ctxt = { hidden $= insert n () } ctxt

unhideName : Name -> Context -> Context
unhideName n ctxt = { hidden $= delete n } ctxt

branchCtxt : Context -> Core Context
branchCtxt ctxt = pure ({ branchDepth $= S } ctxt)

commitCtxt : Context -> Core Context
commitCtxt ctxt
    = case branchDepth ctxt of
           Z => pure ctxt
           S Z => -- add all the things from 'staging' to the real array
                  do let a = content ctxt
                     arr <- get Arr
                     coreLift $ commitStaged (toList (staging ctxt)) arr
                     pure ({ staging := empty,
                             branchDepth := Z } ctxt)
           S k => pure ({ branchDepth := k } ctxt)
  where
    -- We know the array must be big enough, because it will have been resized
    -- if necessary in the branch to fit the index we've been given here
    commitStaged : List (Int, ContextEntry) -> IOArray ContextEntry -> IO ()
    commitStaged [] arr = pure ()
    commitStaged ((idx, val) :: rest) arr
        = do writeArray arr idx val
             commitStaged rest arr

export
newDef : FC -> Name -> RigCount -> List Name ->
         ClosedTerm -> Visibility -> Def -> GlobalDef
newDef fc n rig vars ty vis def
    = MkGlobalDef
        { location = fc
        , fullname = n
        , type = ty
        , eraseArgs = []
        , safeErase = []
        , specArgs = []
        , inferrable = []
        , multiplicity = rig
        , localVars = vars
        , visibility = vis
        , totality = unchecked
        , flags = []
        , refersToM = Nothing
        , refersToRuntimeM = Nothing
        , invertible = False
        , noCycles = False
        , linearChecked = False
        , definition = def
        , compexpr = Nothing
        , namedcompexpr = Nothing
        , sizeChange = []
        , schemeExpr = Nothing
        }

-- Rewrite rules, applied after type checking, for runtime code only
-- LHS and RHS must have the same type, but we don't (currently) require that
-- the result still type checks (which might happen e.g. if transforming to a
-- faster implementation with different behaviour)
-- (Q: Do we need the 'Env' here? Usually we end up needing an 'Env' with a
-- 'NF but we're working with terms rather than values...)
public export
data Transform : Type where
     MkTransform : {vars : _} ->
                   Name -> -- name for identifying the rule
                   Env Term vars -> Term vars -> Term vars -> Transform

||| Types that are transformed into a faster representation
||| during codegen.
public export
data BuiltinType : Type where
    BuiltinNatural : BuiltinType
    NaturalToInteger : BuiltinType
    IntegerToNatural : BuiltinType

export
Show BuiltinType where
    show BuiltinNatural = "Natural"
    show NaturalToInteger = "NaturalToInteger"
    show IntegerToNatural = "IntegerToNatural"

export
getFnName : Transform -> Maybe Name
getFnName (MkTransform _ _ app _)
    = case getFn app of
           Ref _ _ fn => Just fn
           _ => Nothing

-- TODO: refactor via a single function
-- onNames : (Context -> Name -> Core Name) ->
--           (Context -> a    -> Core a)
-- ?
public export
interface HasNames a where
  full : Context -> a -> Core a
  resolved : Context -> a -> Core a

export
HasNames Name where
  full gam (Resolved i)
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                  -- May occasionally happen when working with metadata.
                  -- It's harmless, so just silently return the resolved name.
                | Nothing => pure (Resolved i)
           pure (fullname gdef)
  full gam n = pure n

  resolved gam (Resolved i)
      = pure (Resolved i)
  resolved gam n
      = do let Just i = getNameID n gam
                    | Nothing => pure n
           pure (Resolved i)

export
HasNames UConstraint where
  full gam (ULT x y)
      = do x' <- full gam x; y' <- full gam y
           pure (ULT x' y')
  full gam (ULE x y)
      = do x' <- full gam x; y' <- full gam y
           pure (ULE x' y')

  resolved gam (ULT x y)
      = do x' <- resolved gam x; y' <- resolved gam y
           pure (ULT x' y')
  resolved gam (ULE x y)
      = do x' <- resolved gam x; y' <- resolved gam y
           pure (ULE x' y')

export
HasNames (Term vars) where
  full gam (Ref fc x (Resolved i))
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                | Nothing => pure (Ref fc x (Resolved i))
           pure (Ref fc x (fullname gdef))
  full gam (Meta fc x i xs)
      = do xs <- traverse (full gam) xs
           pure $ case !(lookupCtxtExact (Resolved i) gam) of
             Nothing => Meta fc x i xs
             Just gdef => Meta fc (fullname gdef) i xs
  full gam (Bind fc x b scope)
      = pure (Bind fc x !(traverse (full gam) b) !(full gam scope))
  full gam (App fc fn arg)
      = pure (App fc !(full gam fn) !(full gam arg))
  full gam (As fc s p tm)
      = pure (As fc s !(full gam p) !(full gam tm))
  full gam (TDelayed fc x y)
      = pure (TDelayed fc x !(full gam y))
  full gam (TDelay fc x t y)
      = pure (TDelay fc x !(full gam t) !(full gam y))
  full gam (TForce fc r y)
      = pure (TForce fc r !(full gam y))
  full gam (TType fc (Resolved i))
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                | Nothing => pure (TType fc (Resolved i))
           pure (TType fc (fullname gdef))
  full gam tm = pure tm

  resolved gam (Ref fc x n)
      = do let Just i = getNameID n gam
                | Nothing => pure (Ref fc x n)
           pure (Ref fc x (Resolved i))
  resolved gam (Meta fc x y xs)
      = do xs' <- traverse (resolved gam) xs
           let Just i = getNameID x gam
               | Nothing => pure (Meta fc x y xs')
           pure (Meta fc x i xs')
  resolved gam (Bind fc x b scope)
      = pure (Bind fc x !(traverse (resolved gam) b) !(resolved gam scope))
  resolved gam (App fc fn arg)
      = pure (App fc !(resolved gam fn) !(resolved gam arg))
  resolved gam (As fc s p tm)
      = pure (As fc s !(resolved gam p) !(resolved gam tm))
  resolved gam (TDelayed fc x y)
      = pure (TDelayed fc x !(resolved gam y))
  resolved gam (TDelay fc x t y)
      = pure (TDelay fc x !(resolved gam t) !(resolved gam y))
  resolved gam (TForce fc r y)
      = pure (TForce fc r !(resolved gam y))
  resolved gam (TType fc n)
      = do let Just i = getNameID n gam
                | Nothing => pure (TType fc n)
           pure (TType fc (Resolved i))
  resolved gam tm = pure tm

export
HasNames Pat where
  full gam (PAs fc n p)
     = [| PAs (pure fc) (full gam n) (full gam p) |]
  full gam (PCon fc n i ar ps)
     = [| PCon (pure fc) (full gam n) (pure i) (pure ar) (traverse (full gam) ps) |]
  full gam (PTyCon fc n ar ps)
     = [| PTyCon (pure fc) (full gam n) (pure ar) (traverse (full gam) ps) |]
  full gam p@(PConst _ _) = pure p
  full gam (PArrow fc x p q)
     = [| PArrow (pure fc) (full gam x) (full gam p) (full gam q) |]
  full gam (PDelay fc laz p q)
     = [| PDelay (pure fc) (pure laz) (full gam p) (full gam q) |]
  full gam (PLoc fc n) = PLoc fc <$> full gam n
  full gam (PUnmatchable fc t) = PUnmatchable fc <$> full gam t

  resolved gam (PAs fc n p)
     = [| PAs (pure fc) (resolved gam n) (resolved gam p) |]
  resolved gam (PCon fc n i ar ps)
     = [| PCon (pure fc) (resolved gam n) (pure i) (pure ar) (traverse (resolved gam) ps) |]
  resolved gam (PTyCon fc n ar ps)
     = [| PTyCon (pure fc) (resolved gam n) (pure ar) (traverse (resolved gam) ps) |]
  resolved gam p@(PConst _ _) = pure p
  resolved gam (PArrow fc x p q)
     = [| PArrow (pure fc) (resolved gam x) (resolved gam p) (resolved gam q) |]
  resolved gam (PDelay fc laz p q)
     = [| PDelay (pure fc) (pure laz) (resolved gam p) (resolved gam q) |]
  resolved gam (PLoc fc n) = PLoc fc <$> resolved gam n
  resolved gam (PUnmatchable fc t) = PUnmatchable fc <$> resolved gam t

mutual
  export
  HasNames (CaseTree vars) where
    full gam (Case i v ty alts)
        = pure $ Case i v !(full gam ty) !(traverse (full gam) alts)
    full gam (STerm i tm)
        = pure $ STerm i !(full gam tm)
    full gam t = pure t

    resolved gam (Case i v ty alts)
        = pure $ Case i v !(resolved gam ty) !(traverse (resolved gam) alts)
    resolved gam (STerm i tm)
        = pure $ STerm i !(resolved gam tm)
    resolved gam t = pure t

  export
  HasNames (CaseAlt vars) where
    full gam (ConCase n t args sc)
        = do sc' <- full gam sc
             Just gdef <- lookupCtxtExact n gam
                | Nothing => pure (ConCase n t args sc')
             pure $ ConCase (fullname gdef) t args sc'
    full gam (DelayCase ty arg sc)
        = pure $ DelayCase ty arg !(full gam sc)
    full gam (ConstCase c sc)
        = pure $ ConstCase c !(full gam sc)
    full gam (DefaultCase sc)
        = pure $ DefaultCase !(full gam sc)

    resolved gam (ConCase n t args sc)
        = do sc' <- resolved gam sc
             let Just i = getNameID n gam
                | Nothing => pure (ConCase n t args sc')
             pure $ ConCase (Resolved i) t args sc'
    resolved gam (DelayCase ty arg sc)
        = pure $ DelayCase ty arg !(resolved gam sc)
    resolved gam (ConstCase c sc)
        = pure $ ConstCase c !(resolved gam sc)
    resolved gam (DefaultCase sc)
        = pure $ DefaultCase !(resolved gam sc)

export
HasNames (Env Term vars) where
  full gam [] = pure []
  full gam (b :: bs)
      = pure $ !(traverse (full gam) b) :: !(full gam bs)

  resolved gam [] = pure []
  resolved gam (b :: bs)
      = pure $ !(traverse (resolved gam) b) :: !(resolved gam bs)

export
HasNames Clause where
  full gam (MkClause env lhs rhs)
     = pure $ MkClause !(full gam env) !(full gam lhs) !(full gam rhs)

  resolved gam (MkClause env lhs rhs)
    = [| MkClause (resolved gam env) (resolved gam lhs) (resolved gam rhs) |]


export
HasNames Def where
  full gam (PMDef r args ct rt pats)
      = pure $ PMDef r args !(full gam ct) !(full gam rt)
                     !(traverse fullNamesPat pats)
    where
      fullNamesPat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                     Core (vs ** (Env Term vs, Term vs, Term vs))
      fullNamesPat (_ ** (env, lhs, rhs))
          = pure $ (_ ** (!(full gam env),
                          !(full gam lhs), !(full gam rhs)))
  full gam (TCon t a ps ds u ms cs det)
      = pure $ TCon t a ps ds u !(traverse (full gam) ms)
                                !(traverse (full gam) cs) det
  full gam (BySearch c d def)
      = pure $ BySearch c d !(full gam def)
  full gam (Guess tm b cs)
      = pure $ Guess !(full gam tm) b cs
  full gam t = pure t

  resolved gam (PMDef r args ct rt pats)
      = pure $ PMDef r args !(resolved gam ct) !(resolved gam rt)
                     !(traverse resolvedNamesPat pats)
    where
      resolvedNamesPat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                         Core (vs ** (Env Term vs, Term vs, Term vs))
      resolvedNamesPat (_ ** (env, lhs, rhs))
          = pure $ (_ ** (!(resolved gam env),
                          !(resolved gam lhs), !(resolved gam rhs)))
  resolved gam (TCon t a ps ds u ms cs det)
      = pure $ TCon t a ps ds u !(traverse (resolved gam) ms)
                                !(traverse (resolved gam) cs) det
  resolved gam (BySearch c d def)
      = pure $ BySearch c d !(resolved gam def)
  resolved gam (Guess tm b cs)
      = pure $ Guess !(resolved gam tm) b cs
  resolved gam t = pure t

export
StripNamespace Def where
  trimNS ns (PMDef i args ct rt pats)
      = PMDef i args (trimNS ns ct) rt (map trimNSpat pats)
    where
      trimNSpat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                  (vs ** (Env Term vs, Term vs, Term vs))
      trimNSpat (vs ** (env, lhs, rhs))
          = (vs ** (env, trimNS ns lhs, trimNS ns rhs))
  trimNS ns d = d

  restoreNS ns (PMDef i args ct rt pats)
      = PMDef i args (restoreNS ns ct) rt (map restoreNSpat pats)
    where
      restoreNSpat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                  (vs ** (Env Term vs, Term vs, Term vs))
      restoreNSpat (vs ** (env, lhs, rhs))
          = (vs ** (env, restoreNS ns lhs, restoreNS ns rhs))
  restoreNS ns d = d

export
StripNamespace GlobalDef where
  trimNS ns def = { definition $= trimNS ns } def
  restoreNS ns def = { definition $= restoreNS ns } def

HasNames (NameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(full gam k) v ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(resolved gam k) v ms) ns

export
HasNames PartialReason where
  full gam NotStrictlyPositive = pure NotStrictlyPositive
  full gam (BadCall ns) = pure $ BadCall !(traverse (full gam) ns)
  full gam (RecPath ns) = pure $ RecPath !(traverse (full gam) ns)

  resolved gam NotStrictlyPositive = pure NotStrictlyPositive
  resolved gam (BadCall ns) = pure $ BadCall !(traverse (resolved gam) ns)
  resolved gam (RecPath ns) = pure $ RecPath !(traverse (resolved gam) ns)

export
HasNames Terminating where
  full gam (NotTerminating p) = pure $ NotTerminating !(full gam p)
  full gam t = pure t

  resolved gam (NotTerminating p) = pure $ NotTerminating !(resolved gam p)
  resolved gam t = pure t

export
HasNames Covering where
  full gam IsCovering = pure IsCovering
  full gam (MissingCases ts)
      = pure $ MissingCases !(traverse (full gam) ts)
  full gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (full gam) ns)

  resolved gam IsCovering = pure IsCovering
  resolved gam (MissingCases ts)
      = pure $ MissingCases !(traverse (resolved gam) ts)
  resolved gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (resolved gam) ns)

export
HasNames CaseError where
  full gam DifferingArgNumbers = pure DifferingArgNumbers
  full gam DifferingTypes = pure DifferingTypes
  full gam (MatchErased (vs ** (rho, t))) = do
    rho <- full gam rho
    t <- full gam t
    pure (MatchErased (vs ** (rho, t)))
  full gam (NotFullyApplied n) = NotFullyApplied <$> full gam n
  full gam UnknownType = pure UnknownType

  resolved gam DifferingArgNumbers = pure DifferingArgNumbers
  resolved gam DifferingTypes = pure DifferingTypes
  resolved gam (MatchErased (vs ** (rho, t))) = do
    rho <- resolved gam rho
    t <- resolved gam t
    pure (MatchErased (vs ** (rho, t)))
  resolved gam (NotFullyApplied n) = NotFullyApplied <$> resolved gam n
  resolved gam UnknownType = pure UnknownType


export
HasNames Warning where
  full gam (ParserWarning fc x) = pure (ParserWarning fc x)
  full gam (UnreachableClause fc rho s) = UnreachableClause fc <$> full gam rho <*> full gam s
  full gam (ShadowingGlobalDefs fc xs)
    = ShadowingGlobalDefs fc <$> traverseList1 (traversePair (traverseList1 (full gam))) xs
  full gam w@(ShadowingLocalBindings _ _) = pure w
  full gam (Deprecated x y) = Deprecated x <$> traverseOpt (traversePair (full gam)) y
  full gam (GenericWarn x) = pure (GenericWarn x)

  resolved gam (ParserWarning fc x) = pure (ParserWarning fc x)
  resolved gam (UnreachableClause fc rho s) = UnreachableClause fc <$> resolved gam rho <*> resolved gam s
  resolved gam (ShadowingGlobalDefs fc xs)
    = ShadowingGlobalDefs fc <$> traverseList1 (traversePair (traverseList1 (resolved gam))) xs
  resolved gam w@(ShadowingLocalBindings _ _) = pure w
  resolved gam (Deprecated x y) = Deprecated x <$> traverseOpt (traversePair (resolved gam)) y
  resolved gam (GenericWarn x) = pure (GenericWarn x)

export
HasNames Error where
  full gam (Fatal err) = Fatal <$> full gam err
  full _ (CantConvert fc gam rho s t)
    = CantConvert fc gam <$> full gam rho <*> full gam s <*> full gam t
  full _ (CantSolveEq fc gam rho s t)
    = CantSolveEq fc gam <$> full gam rho <*> full gam s <*> full gam t
  full gam (PatternVariableUnifies fc fct rho n s)
    = PatternVariableUnifies fc fct <$> full gam rho <*> full gam n <*> full gam s
  full gam (CyclicMeta fc rho n s)
    = CyclicMeta fc <$> full gam rho <*> full gam n <*> full gam s
  full _ (WhenUnifying fc gam rho s t err)
    = WhenUnifying fc gam <$> full gam rho <*> full gam s <*> full gam t <*> full gam err
  full gam (ValidCase fc rho x)
    = ValidCase fc <$> full gam rho <*> either (map Left . full gam) (map Right . full gam) x
  full gam (UndefinedName fc n) = UndefinedName fc <$> full gam n
  full gam (InvisibleName fc n mns) = InvisibleName fc <$> full gam n <*> pure mns
  full gam (BadTypeConType fc n) = BadTypeConType fc <$> full gam n
  full gam (BadDataConType fc n n') = BadDataConType fc <$> full gam n <*> full gam n'
  full gam (NotCovering fc n cov) = NotCovering fc <$> full gam n <*> full gam cov
  full gam (NotTotal fc n pr) = NotTotal fc <$> full gam n <*> full gam pr
  full gam (LinearUsed fc k n) = LinearUsed fc k <$> full gam n
  full gam (LinearMisuse fc n x y) = LinearMisuse fc <$> full gam n <*> pure x <*> pure y
  full gam (BorrowPartial fc rho s t) = BorrowPartial fc <$> full gam rho <*> full gam s <*> full gam t
  full gam (BorrowPartialType fc rho s) = BorrowPartialType fc <$> full gam rho <*> full gam s
  full gam (AmbiguousName fc xs) = AmbiguousName fc <$> traverse (full gam) xs
  full gam (AmbiguousElab fc rho xs)
    = AmbiguousElab fc <$> full gam rho <*> traverse (\ (gam, t) => (gam,) <$> full gam t) xs
  full gam (AmbiguousSearch fc rho s xs)
    = AmbiguousSearch fc <$> full gam rho <*> full gam s <*> traverse (full gam) xs
  full gam (AmbiguityTooDeep fc n xs) = AmbiguityTooDeep fc <$> full gam n <*> traverse (full gam) xs
  full gam (AllFailed xs)
     = map AllFailed $ for xs $ \ (mn, err) =>
         (,) <$> traverseOpt (full gam) mn <*> full gam err
  full gam (RecordTypeNeeded fc rho) = RecordTypeNeeded fc <$> full gam rho
  full gam (DuplicatedRecordUpdatePath fc xs) = pure (DuplicatedRecordUpdatePath fc xs)
  full gam (NotRecordField fc x mn) = NotRecordField fc x <$> traverseOpt (full gam) mn
  full gam (NotRecordType fc n) = NotRecordType fc <$> full gam n
  full gam (IncompatibleFieldUpdate fc xs) = pure (IncompatibleFieldUpdate fc xs)
  full gam (InvalidArgs fc rho xs s) = InvalidArgs fc <$> full gam rho <*> traverse (full gam) xs <*> full gam s
  full gam (TryWithImplicits fc rho xs)
    = TryWithImplicits fc <$> full gam rho
       <*> for xs (\ (n, t) => (,) <$> full gam n <*> full gam t)
  full gam (BadUnboundImplicit fc rho n s) = BadUnboundImplicit fc <$> full gam rho <*> full gam n <*> full gam s
  full _ (CantSolveGoal fc gam rho s merr)
    = CantSolveGoal fc gam <$> full gam rho <*> full gam s <*> traverseOpt (full gam) merr
  full gam (DeterminingArg fc n x rho s)
    = DeterminingArg fc <$> full gam n <*> pure x <*> full gam rho <*> full gam s
  full gam (UnsolvedHoles xs) = UnsolvedHoles <$> traverse (traversePair (full gam)) xs
  full gam (CantInferArgType fc rho n n1 s)
    = CantInferArgType fc <$> full gam rho <*> full gam n <*> full gam n1 <*> full gam s
  full gam (SolvedNamedHole fc rho n s) = SolvedNamedHole fc <$> full gam rho <*> full gam n <*> full gam s
  full gam (VisibilityError fc x n y n1) = VisibilityError fc x <$> full gam n <*> pure y <*> full gam n1
  full gam (NonLinearPattern fc n) = NonLinearPattern fc <$> full gam  n
  full gam (BadPattern fc n) = BadPattern fc <$> full gam n
  full gam (NoDeclaration fc n) = NoDeclaration fc <$> full gam n
  full gam (AlreadyDefined fc n) = AlreadyDefined fc <$> full gam n
  full gam (NotFunctionType fc rho s) = NotFunctionType fc <$> full gam rho <*> full gam s
  full gam (RewriteNoChange fc rho s t) = RewriteNoChange fc <$> full gam rho <*> full gam s <*> full gam t
  full gam (NotRewriteRule fc rho s) = NotRewriteRule fc <$> full gam rho <*> full gam s
  full gam (CaseCompile fc n x) = CaseCompile fc <$> full gam n <*> full gam x
  full gam (MatchTooSpecific fc rho s) = MatchTooSpecific fc <$> full gam rho <*> full gam s
  full gam (BadDotPattern fc rho x s t)
    = BadDotPattern fc <$> full gam rho <*> pure x <*> full gam s <*> full gam t
  full gam (BadImplicit fc x) = pure (BadImplicit fc x)
  full gam (BadRunElab fc rho s desc) = BadRunElab fc <$> full gam rho <*> full gam s <*> pure desc
  full gam (RunElabFail e) = RunElabFail <$> full gam e
  full gam (GenericMsg fc x) = pure (GenericMsg fc x)
  full gam (TTCError x) = pure (TTCError x)
  full gam (FileErr x y) = pure (FileErr x y)
  full gam (CantFindPackage x) = pure (CantFindPackage x)
  full gam (LitFail fc) = pure (LitFail fc)
  full gam (LexFail fc x) = pure (LexFail fc x)
  full gam (ParseFail xs) = pure (ParseFail xs)
  full gam (ModuleNotFound fc x) = pure (ModuleNotFound fc x)
  full gam (CyclicImports xs) = pure (CyclicImports xs)
  full gam ForceNeeded = pure ForceNeeded
  full gam (InternalError x) = pure (InternalError x)
  full gam (UserError x) = pure (UserError x)
  full gam (NoForeignCC fc xs) = pure (NoForeignCC fc xs)
  full gam (BadMultiline fc x) = pure (BadMultiline fc x)
  full gam (Timeout x) = pure (Timeout x)
  full gam (FailingDidNotFail fc) = pure (FailingDidNotFail fc)
  full gam (FailingWrongError fc x err) = FailingWrongError fc x <$> traverseList1 (full gam) err
  full gam (InType fc n err) = InType fc <$> full gam n <*> full gam err
  full gam (InCon fc n err) = InCon fc <$> full gam n <*> full gam err
  full gam (InLHS fc n err) = InLHS fc <$> full gam n <*> full gam err
  full gam (InRHS fc n err) = InRHS fc <$> full gam n <*> full gam err
  full gam (MaybeMisspelling err xs) = MaybeMisspelling <$> full gam err <*> pure xs
  full gam (WarningAsError wrn) = WarningAsError <$> full gam wrn

  resolved gam (Fatal err) = Fatal <$> resolved gam err
  resolved _ (CantConvert fc gam rho s t)
    = CantConvert fc gam <$> resolved gam rho <*> resolved gam s <*> resolved gam t
  resolved _ (CantSolveEq fc gam rho s t)
    = CantSolveEq fc gam <$> resolved gam rho <*> resolved gam s <*> resolved gam t
  resolved gam (PatternVariableUnifies fc fct rho n s)
    = PatternVariableUnifies fc fct <$> resolved gam rho <*> resolved gam n <*> resolved gam s
  resolved gam (CyclicMeta fc rho n s)
    = CyclicMeta fc <$> resolved gam rho <*> resolved gam n <*> resolved gam s
  resolved _ (WhenUnifying fc gam rho s t err)
    = WhenUnifying fc gam <$> resolved gam rho <*> resolved gam s <*> resolved gam t <*> resolved gam err
  resolved gam (ValidCase fc rho x)
    = ValidCase fc <$> resolved gam rho <*> either (map Left . resolved gam) (map Right . resolved gam) x
  resolved gam (UndefinedName fc n) = UndefinedName fc <$> resolved gam n
  resolved gam (InvisibleName fc n mns) = InvisibleName fc <$> resolved gam n <*> pure mns
  resolved gam (BadTypeConType fc n) = BadTypeConType fc <$> resolved gam n
  resolved gam (BadDataConType fc n n') = BadDataConType fc <$> resolved gam n <*> resolved gam n'
  resolved gam (NotCovering fc n cov) = NotCovering fc <$> resolved gam n <*> resolved gam cov
  resolved gam (NotTotal fc n pr) = NotTotal fc <$> resolved gam n <*> resolved gam pr
  resolved gam (LinearUsed fc k n) = LinearUsed fc k <$> resolved gam n
  resolved gam (LinearMisuse fc n x y) = LinearMisuse fc <$> resolved gam n <*> pure x <*> pure y
  resolved gam (BorrowPartial fc rho s t) = BorrowPartial fc <$> resolved gam rho <*> resolved gam s <*> resolved gam t
  resolved gam (BorrowPartialType fc rho s) = BorrowPartialType fc <$> resolved gam rho <*> resolved gam s
  resolved gam (AmbiguousName fc xs) = AmbiguousName fc <$> traverse (resolved gam) xs
  resolved gam (AmbiguousElab fc rho xs)
    = AmbiguousElab fc <$> resolved gam rho <*> traverse (\ (gam, t) => (gam,) <$> resolved gam t) xs
  resolved gam (AmbiguousSearch fc rho s xs)
    = AmbiguousSearch fc <$> resolved gam rho <*> resolved gam s <*> traverse (resolved gam) xs
  resolved gam (AmbiguityTooDeep fc n xs) = AmbiguityTooDeep fc <$> resolved gam n <*> traverse (resolved gam) xs
  resolved gam (AllFailed xs)
     = map AllFailed $ for xs $ \ (mn, err) =>
         (,) <$> traverseOpt (resolved gam) mn <*> resolved gam err
  resolved gam (RecordTypeNeeded fc rho) = RecordTypeNeeded fc <$> resolved gam rho
  resolved gam (DuplicatedRecordUpdatePath fc xs) = pure (DuplicatedRecordUpdatePath fc xs)
  resolved gam (NotRecordField fc x mn) = NotRecordField fc x <$> traverseOpt (resolved gam) mn
  resolved gam (NotRecordType fc n) = NotRecordType fc <$> resolved gam n
  resolved gam (IncompatibleFieldUpdate fc xs) = pure (IncompatibleFieldUpdate fc xs)
  resolved gam (InvalidArgs fc rho xs s) = InvalidArgs fc <$> resolved gam rho <*> traverse (resolved gam) xs <*> resolved gam s
  resolved gam (TryWithImplicits fc rho xs)
    = TryWithImplicits fc <$> resolved gam rho
       <*> for xs (\ (n, t) => (,) <$> resolved gam n <*> resolved gam t)
  resolved gam (BadUnboundImplicit fc rho n s) = BadUnboundImplicit fc <$> resolved gam rho <*> resolved gam n <*> resolved gam s
  resolved _ (CantSolveGoal fc gam rho s merr)
    = CantSolveGoal fc gam <$> resolved gam rho <*> resolved gam s <*> traverseOpt (resolved gam) merr
  resolved gam (DeterminingArg fc n x rho s)
    = DeterminingArg fc <$> resolved gam n <*> pure x <*> resolved gam rho <*> resolved gam s
  resolved gam (UnsolvedHoles xs) = UnsolvedHoles <$> traverse (traversePair (resolved gam)) xs
  resolved gam (CantInferArgType fc rho n n1 s)
    = CantInferArgType fc <$> resolved gam rho <*> resolved gam n <*> resolved gam n1 <*> resolved gam s
  resolved gam (SolvedNamedHole fc rho n s) = SolvedNamedHole fc <$> resolved gam rho <*> resolved gam n <*> resolved gam s
  resolved gam (VisibilityError fc x n y n1) = VisibilityError fc x <$> resolved gam n <*> pure y <*> resolved gam n1
  resolved gam (NonLinearPattern fc n) = NonLinearPattern fc <$> resolved gam  n
  resolved gam (BadPattern fc n) = BadPattern fc <$> resolved gam n
  resolved gam (NoDeclaration fc n) = NoDeclaration fc <$> resolved gam n
  resolved gam (AlreadyDefined fc n) = AlreadyDefined fc <$> resolved gam n
  resolved gam (NotFunctionType fc rho s) = NotFunctionType fc <$> resolved gam rho <*> resolved gam s
  resolved gam (RewriteNoChange fc rho s t) = RewriteNoChange fc <$> resolved gam rho <*> resolved gam s <*> resolved gam t
  resolved gam (NotRewriteRule fc rho s) = NotRewriteRule fc <$> resolved gam rho <*> resolved gam s
  resolved gam (CaseCompile fc n x) = CaseCompile fc <$> resolved gam n <*> resolved gam x
  resolved gam (MatchTooSpecific fc rho s) = MatchTooSpecific fc <$> resolved gam rho <*> resolved gam s
  resolved gam (BadDotPattern fc rho x s t)
    = BadDotPattern fc <$> resolved gam rho <*> pure x <*> resolved gam s <*> resolved gam t
  resolved gam (BadImplicit fc x) = pure (BadImplicit fc x)
  resolved gam (BadRunElab fc rho s desc) = BadRunElab fc <$> resolved gam rho <*> resolved gam s <*> pure desc
  resolved gam (RunElabFail e) = RunElabFail <$> resolved gam e
  resolved gam (GenericMsg fc x) = pure (GenericMsg fc x)
  resolved gam (TTCError x) = pure (TTCError x)
  resolved gam (FileErr x y) = pure (FileErr x y)
  resolved gam (CantFindPackage x) = pure (CantFindPackage x)
  resolved gam (LitFail fc) = pure (LitFail fc)
  resolved gam (LexFail fc x) = pure (LexFail fc x)
  resolved gam (ParseFail xs) = pure (ParseFail xs)
  resolved gam (ModuleNotFound fc x) = pure (ModuleNotFound fc x)
  resolved gam (CyclicImports xs) = pure (CyclicImports xs)
  resolved gam ForceNeeded = pure ForceNeeded
  resolved gam (InternalError x) = pure (InternalError x)
  resolved gam (UserError x) = pure (UserError x)
  resolved gam (NoForeignCC fc xs) = pure (NoForeignCC fc xs)
  resolved gam (BadMultiline fc x) = pure (BadMultiline fc x)
  resolved gam (Timeout x) = pure (Timeout x)
  resolved gam (FailingDidNotFail fc) = pure (FailingDidNotFail fc)
  resolved gam (FailingWrongError fc x err) = FailingWrongError fc x <$> traverseList1 (resolved gam) err
  resolved gam (InType fc n err) = InType fc <$> resolved gam n <*> resolved gam err
  resolved gam (InCon fc n err) = InCon fc <$> resolved gam n <*> resolved gam err
  resolved gam (InLHS fc n err) = InLHS fc <$> resolved gam n <*> resolved gam err
  resolved gam (InRHS fc n err) = InRHS fc <$> resolved gam n <*> resolved gam err
  resolved gam (MaybeMisspelling err xs) = MaybeMisspelling <$> resolved gam err <*> pure xs
  resolved gam (WarningAsError wrn) = WarningAsError <$> resolved gam wrn

export
HasNames Totality where
  full gam (MkTotality t c) = pure $ MkTotality !(full gam t) !(full gam c)
  resolved gam (MkTotality t c) = pure $ MkTotality !(resolved gam t) !(resolved gam c)

export
HasNames SCCall where
  full gam sc = pure $ { fnCall := !(full gam (fnCall sc)) } sc
  resolved gam sc = pure $ { fnCall := !(resolved gam (fnCall sc)) } sc

export
HasNames a => HasNames (Maybe a) where
  full gam Nothing = pure Nothing
  full gam (Just x) = pure $ Just !(full gam x)
  resolved gam Nothing = pure Nothing
  resolved gam (Just x) = pure $ Just !(resolved gam x)

export
HasNames GlobalDef where
  full gam def
      = do
--            ts <- full gam (type def)
--            d <- full gam (definition def)
--            coreLift $ printLn (fullname def, ts)
--            coreLift $ printLn (fullname def, d)
           pure $ { type := !(full gam (type def)),
                    definition := !(full gam (definition def)),
                    totality := !(full gam (totality def)),
                    refersToM := !(full gam (refersToM def)),
                    refersToRuntimeM := !(full gam (refersToRuntimeM def)),
                    sizeChange := !(traverse (full gam) (sizeChange def))
                  } def
  resolved gam def
      = pure $ { type := !(resolved gam (type def)),
                 definition := !(resolved gam (definition def)),
                 totality := !(resolved gam (totality def)),
                 refersToM := !(resolved gam (refersToM def)),
                 refersToRuntimeM := !(resolved gam (refersToRuntimeM def)),
                 sizeChange := !(traverse (resolved gam) (sizeChange def))
               } def

export
HasNames Transform where
  full gam (MkTransform n env lhs rhs)
      = pure $ MkTransform !(full gam n) !(full gam env)
                           !(full gam lhs) !(full gam rhs)

  resolved gam (MkTransform n env lhs rhs)
      = pure $ MkTransform !(resolved gam n) !(resolved gam env)
                           !(resolved gam lhs) !(resolved gam rhs)

-- Return all the currently defined names
export
allNames : Context -> Core (List Name)
allNames ctxt = traverse (full ctxt) $ map Resolved [1..nextEntry ctxt - 1]

public export
record Defs where
  constructor MkDefs
  gamma : Context
  mutData : List Name -- Currently declared but undefined data types
  currentNS : Namespace -- namespace for current definitions
  nestedNS : List Namespace -- other nested namespaces we can look in
  options : Options
  toSave : NameMap ()
  nextTag : Int
  typeHints : NameMap (List (Name, Bool))
     -- ^ a mapping from type names to hints (and a flag setting whether it's
     -- a "direct" hint). Direct hints are searched first (as part of a group)
     -- the indirect hints. Indirect hints, in practice, are used to find
     -- instances of parent interfaces, and we don't search these until we've
     -- tried to find a direct result via a constructor or a top level hint.
  autoHints : NameMap Bool
     -- ^ global search hints. A mapping from the hint name, to whether it is
     -- a "default hint". A default hint is used only if all other attempts
     -- to search fail (this flag is really only intended as a mechanism
     -- for defaulting of literals)
  openHints : NameMap ()
     -- ^ currently open global hints; just for the rest of this module (not exported)
     -- and prioritised
  localHints : NameMap ()
     -- ^ Hints defined in the current environment
  saveTypeHints : List (Name, Name, Bool)
     -- We don't look up anything in here, it's merely for saving out to TTC.
     -- We save the hints in the 'GlobalDef' itself for faster lookup.
  saveAutoHints : List (Name, Bool)
  transforms : NameMap (List Transform)
     -- ^ A mapping from names to transformation rules which update applications
     -- of that name
  saveTransforms : List (Name, Transform)
  namedirectives : NameMap (List String)
  ifaceHash : Int
  importHashes : List (Namespace, Int)
     -- ^ interface hashes of imported modules
  imported : List (ModuleIdent, Bool, Namespace)
     -- ^ imported modules, whether to rexport, as namespace
  allImported : List (String, (ModuleIdent, Bool, Namespace))
     -- ^ all imported filenames/namespaces, just to avoid loading something
     -- twice unnecessarily (this is a record of all the things we've
     -- called 'readFromTTC' with, in practice)
  cgdirectives : List (CG, String)
     -- ^ Code generator directives, which are free form text and thus to
     -- be interpreted however the specific code generator requires
  toCompileCase : List Name
     -- ^ Names which need to be compiled to run time case trees
  incData : List (CG, String, List String)
     -- ^ What we've compiled incrementally for this module: codegen,
     -- object file, any additional CG dependent data (e.g. linker flags)
  allIncData : List (CG, List String, List String)
     -- ^ Incrementally compiled files for all imports. Only lists CGs for
     -- while all modules have associated incremental compile data
  toIR : NameMap ()
     -- ^ Names which need to be compiled to IR at the end of processing
     -- the current module
  userHoles : NameMap Bool
     -- ^ Metavariables the user still has to fill in. In practice, that's
     -- everything with a user accessible name and a definition of Hole.
     -- The Bool says whether it was introduced in another module.
  peFailures : NameMap ()
     -- ^ Partial evaluation names which have failed, so don't bother trying
     -- again
  timings : StringMap (Bool, Integer)
     -- ^ record of timings from logTimeRecord
  timer : Maybe (Integer, String)
     -- ^ for timing and checking timeouts; the maximum time after which a
     -- timeout should be thrown
  warnings : List Warning
     -- ^ as yet unreported warnings
  schemeEvalLoaded : Bool
  foreignExports : NameMap (List (String, String))
       -- ^ For functions which are callable from a foreign language. This
       -- maps names to a pair of the back end and the exported function name

-- Label for context references
export
data Ctxt : Type where


export
clearDefs : Defs -> Core Defs
clearDefs defs
    = pure ({ gamma->inlineOnly := True } defs)

export
initDefs : Core Defs
initDefs
    = do gam <- initCtxt
         opts <- defaults
         pure $ MkDefs
           { gamma = gam
           , mutData = []
           , currentNS = mainNS
           , nestedNS = []
           , options = opts
           , toSave = empty
           , nextTag = 100
           , typeHints = empty
           , autoHints = empty
           , openHints = empty
           , localHints = empty
           , saveTypeHints = []
           , saveAutoHints = []
           , transforms = empty
           , saveTransforms = []
           , namedirectives = empty
           , ifaceHash = 5381
           , importHashes = []
           , imported = []
           , allImported = []
           , cgdirectives = []
           , toCompileCase = []
           , incData = []
           , allIncData = []
           , toIR = empty
           , userHoles = empty
           , peFailures = empty
           , timings = empty
           , timer = Nothing
           , warnings = []
           , schemeEvalLoaded = False
           , foreignExports = empty
           }

-- Reset the context, except for the options
export
clearCtxt : {auto c : Ref Ctxt Defs} ->
            Core ()
clearCtxt
    = do defs <- get Ctxt
         put Ctxt ({ options := resetElab (options defs),
                     timings := timings defs } !initDefs)
  where
    resetElab : Options -> Options
    resetElab opts =
      let tot = totalReq (session opts) in
      { elabDirectives := { totality := tot } defaultElab } opts

export
getFieldNames : Context -> Namespace -> List Name
getFieldNames ctxt recNS
  = let nms = resolvedAs ctxt in
    keys $ flip filterBy nms $ \ n =>
      case isRF n of
        Nothing => False
        Just (ns, field) => ns == recNS

-- Find similar looking names in the context
export
getSimilarNames : {auto c : Ref Ctxt Defs} ->
                   Name -> Core (Maybe (String, List (Name, Visibility, Nat)))
getSimilarNames nm = case show <$> userNameRoot nm of
  Nothing => pure Nothing
  Just str => if length str <= 1 then pure (Just (str, [])) else
    do defs <- get Ctxt
       let threshold : Nat := max 1 (assert_total (divNat (length str) 3))
       let test : Name -> Core (Maybe (Visibility, Nat)) := \ nm => do
               let (Just str') = show <$> userNameRoot nm
                   | _ => pure Nothing
               dist <- coreLift $ Levenshtein.compute str str'
               let True = dist <= threshold
                   | False => pure Nothing
               Just def <- lookupCtxtExact nm (gamma defs)
                   | Nothing => pure Nothing -- should be impossible
               pure (Just (visibility def, dist))
       kept <- NameMap.mapMaybeM @{CORE} test (resolvedAs (gamma defs))
       pure $ Just (str, toList kept)

export
showSimilarNames : Namespace -> Name -> String ->
                   List (Name, Visibility, Nat) -> List String
showSimilarNames ns nm str kept
  = let (loc, priv) := partitionEithers $ kept <&> \ (nm', vis, n) =>
                         let False = fst (splitNS nm') `isParentOf` ns
                               | _ => Left (nm', n)
                             Private = vis
                               | _ => Left (nm', n)
                         in Right (nm', n)
        sorted      := sortBy (compare `on` snd)
        roots1      := mapMaybe (showNames nm str False . fst) (sorted loc)
        roots2      := mapMaybe (showNames nm str True  . fst) (sorted priv)
    in nub roots1 ++ nub roots2

  where

  showNames : Name -> String -> Bool -> Name -> Maybe String
  showNames target str priv nm = do
    let adj  = if priv then " (not exported)" else ""
    let root = nameRoot nm
    let True = str == root
      | _ => pure (root ++ adj)
    let full = show (pretty nm)
    let True = (str == full || show target == full) && not priv
      | _ => pure (full ++ adj)
    Nothing


getVisibility : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Visibility
getVisibility fc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName fc n)
         pure $ visibility def

maybeMisspelling : {auto c : Ref Ctxt Defs} ->
                   Error -> Name -> Core a
maybeMisspelling err nm = do
  ns <- currentNS <$> get Ctxt
  Just (str, kept) <- getSimilarNames nm
    | Nothing => throw err
  let candidates = showSimilarNames ns nm str kept
  case candidates of
    [] => throw err
    (x::xs) => throw (MaybeMisspelling err (x ::: xs))

-- Throw an UndefinedName exception. But try to find similar names first.
export
undefinedName : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core a
undefinedName loc nm = maybeMisspelling (UndefinedName loc nm) nm

-- Throw a NoDeclaration exception. But try to find similar names first.
export
noDeclaration : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core a
noDeclaration loc nm = maybeMisspelling (NoDeclaration loc nm) nm

export
ambiguousName : {auto c : Ref Ctxt Defs} -> FC
             -> Name -> List Name
             -> Core a
ambiguousName fc n ns = do
  ns <- filterM (\x => pure $ !(getVisibility fc x) /= Private) ns
  case ns of
    [] =>         undefinedName fc n
    ns => throw $ AmbiguousName fc ns

-- Get the canonical name of something that might have been aliased via
-- import as
export
canonicalName : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Name
canonicalName fc n
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [(n, _, _)] => pure n
              ns => ambiguousName fc n (map fst ns)

-- If the name is aliased, get the alias
export
aliasName : {auto c : Ref Ctxt Defs} ->
            Name -> Core Name
aliasName fulln
    = do defs <- get Ctxt
         let Just r = userNameRoot fulln
                | Nothing => pure fulln
         let Just ps = lookup r (possibles (gamma defs))
                | Nothing => pure fulln
         findAlias ps
  where
    findAlias : List PossibleName -> Core Name
    findAlias [] = pure fulln
    findAlias (Alias as full i :: ps)
        = if full == fulln
             then pure as
             else findAlias ps
    findAlias (_ :: ps) = findAlias ps

-- Beware: if your hashable thing contains (potentially resolved) names,
-- it'll be better to use addHashWithNames to make the hash independent
-- of the internal numbering of names.
export
addHash : {auto c : Ref Ctxt Defs} -> Hashable a => a -> Core ()
addHash x = update Ctxt { ifaceHash $= flip hashWithSalt x }

export
initHash : {auto c : Ref Ctxt Defs} -> Core ()
initHash = update Ctxt { ifaceHash := 5381 }

export
addUserHole : {auto c : Ref Ctxt Defs} ->
              Bool -> -- defined in another module?
              Name -> -- hole name
              Core ()
addUserHole ext n = update Ctxt { userHoles $= insert n ext }

export
clearUserHole : {auto c : Ref Ctxt Defs} -> Name -> Core ()
clearUserHole n = update Ctxt { userHoles $= delete n }

export
getUserHoles : {auto c : Ref Ctxt Defs} ->
               Core (List Name)
getUserHoles
    = do defs <- get Ctxt
         let hs = sort (keys (userHoles defs))
         filterM (isHole defs) hs
  where
    -- If a hole is declared in one file and defined in another, its
    -- name won't have been cleared unless we've already looked up its
    -- definition (as addDef needs to be called to clear it). So here
    -- check that it's really a hole
    isHole : Defs -> Name -> Core Bool
    isHole defs n
        = do Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure True
             pure $ case definition def of
                  None => True
                  Hole _ _ => True
                  _ => False

export
addDef : {auto c : Ref Ctxt Defs} ->
         Name -> GlobalDef -> Core Int
addDef n def
    = do defs <- get Ctxt
         (idx, gam') <- addCtxt n def (gamma defs)
         put Ctxt ({ gamma := gam' } defs)
         case definition def of
              None => pure ()
              Hole _ _ => pure ()
              _ => clearUserHole (fullname def)
         pure idx

export
addContextEntry : {auto c : Ref Ctxt Defs} ->
                  Namespace -> Name -> Binary -> Core Int
addContextEntry ns n def
    = do defs <- get Ctxt
         (idx, gam') <- addEntry n (Coded ns def) (gamma defs)
         put Ctxt ({ gamma := gam' } defs)
         pure idx

export
addContextAlias : {auto c : Ref Ctxt Defs} ->
                  Name -> Name -> Core ()
addContextAlias alias full
    = do defs <- get Ctxt
         Nothing <- lookupCtxtExact alias (gamma defs)
             | _ => pure () -- Don't add the alias if the name exists already
         gam' <- newAlias alias full (gamma defs)
         put Ctxt ({ gamma := gam' } defs)

export
addBuiltin : {arity : _} ->
             {auto x : Ref Ctxt Defs} ->
             Name -> ClosedTerm -> Totality ->
             PrimFn arity -> Core ()
addBuiltin n ty tot op
   = do ignore $
       addDef n $ MkGlobalDef
         { location = emptyFC
         , fullname = n
         , type = ty
         , eraseArgs = []
         , safeErase = []
         , specArgs = []
         , inferrable = []
         , multiplicity = top
         , localVars = []
         , visibility = Public
         , totality = tot
         , flags = [Inline]
         , refersToM = Nothing
         , refersToRuntimeM = Nothing
         , invertible = False
         , noCycles = False
         , linearChecked = True
         , definition = Builtin op
         , compexpr = Nothing
         , namedcompexpr = Nothing
         , sizeChange = []
         , schemeExpr = Nothing
         }

export
updateDef : {auto c : Ref Ctxt Defs} ->
            Name -> (Def -> Maybe Def) -> Core ()
updateDef n fdef
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => pure ()
         case fdef (definition gdef) of
              Nothing => pure ()
              Just def' => ignore $ addDef n ({ definition := def',
                                                schemeExpr := Nothing } gdef)

export
updateTy : {auto c : Ref Ctxt Defs} ->
           Int -> ClosedTerm -> Core ()
updateTy i ty
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure ()
         ignore $ addDef (Resolved i) ({ type := ty } gdef)

export
setCompiled : {auto c : Ref Ctxt Defs} ->
              Name -> CDef -> Core ()
setCompiled n cexp
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         ignore $ addDef n ({ compexpr := Just cexp } gdef)

-- Record that the name has been linearity checked so we don't need to do
-- it again
export
setLinearCheck : {auto c : Ref Ctxt Defs} ->
                 Int -> Bool -> Core ()
setLinearCheck i chk
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure ()
         ignore $ addDef (Resolved i) ({ linearChecked := chk } gdef)

export
setCtxt : {auto c : Ref Ctxt Defs} -> Context -> Core ()
setCtxt gam = update Ctxt { gamma := gam }

export
resolveName : {auto c : Ref Ctxt Defs} ->
            Name -> Core Int
resolveName (Resolved idx) = pure idx
resolveName n
  = do defs <- get Ctxt
       (i, gam') <- getPosition n (gamma defs)
       setCtxt gam'
       pure i

export
addName : {auto c : Ref Ctxt Defs} ->
          Name -> Core Int
addName (Resolved idx) = pure idx
addName n
  = do defs <- get Ctxt
       (i, gam') <- newEntry n (gamma defs)
       setCtxt gam'
       pure i

-- Call this before trying alternative elaborations, so that updates to the
-- context are put in the staging area rather than writing over the mutable
-- array of definitions.
-- Returns the old context (the one we'll go back to if the branch fails)
export
branch : {auto c : Ref Ctxt Defs} ->
       Core Defs
branch
  = do ctxt <- get Ctxt
       gam' <- branchCtxt (gamma ctxt)
       setCtxt gam'
       pure ctxt

-- Call this after trying an elaboration to commit any changes to the mutable
-- array of definitions once we know they're correct. Only actually commits
-- when we're right back at the top level
export
commit : {auto c : Ref Ctxt Defs} ->
       Core ()
commit
  = do defs <- get Ctxt
       gam' <- commitCtxt (gamma defs)
       setCtxt gam'

export
depth : {auto c : Ref Ctxt Defs} ->
      Core Nat
depth
  = do defs <- get Ctxt
       pure (branchDepth (gamma defs))

export
dumpStaging : {auto c : Ref Ctxt Defs} ->
              Core ()
dumpStaging
    = do defs <- get Ctxt
         coreLift $ putStrLn $ "Staging area: " ++ show (keys (staging (gamma defs)))

-- Explicitly note that the name should be saved when writing out a .ttc
export
addToSave : {auto c : Ref Ctxt Defs} ->
          Name -> Core ()
addToSave n_in
  = do defs <- get Ctxt
       n <- full (gamma defs) n_in
       put Ctxt ({ toSave $= insert n (),
                   toIR $= insert n ()
                 } defs)

-- Specific lookup functions
export
lookupExactBy : (GlobalDef -> a) -> Name -> Context ->
              Core (Maybe a)
lookupExactBy fn n gam
  = do Just gdef <- lookupCtxtExact n gam
            | Nothing => pure Nothing
       pure (Just (fn gdef))

export
lookupNameBy : (GlobalDef -> a) -> Name -> Context ->
             Core (List (Name, Int, a))
lookupNameBy fn n gam
  = do gdef <- lookupCtxtName n gam
       pure (map (\ (n, i, gd) => (n, i, fn gd)) gdef)

export
lookupDefExact : Name -> Context -> Core (Maybe Def)
lookupDefExact = lookupExactBy definition

export
lookupDefName : Name -> Context -> Core (List (Name, Int, Def))
lookupDefName = lookupNameBy definition

export
lookupTyExact : Name -> Context -> Core (Maybe ClosedTerm)
lookupTyExact = lookupExactBy type

export
lookupTyName : Name -> Context -> Core (List (Name, Int, ClosedTerm))
lookupTyName = lookupNameBy type

export
lookupDefTyExact : Name -> Context -> Core (Maybe (Def, ClosedTerm))
lookupDefTyExact = lookupExactBy (\g => (definition g, type g))

-- private names are only visible in this namespace if their namespace
-- is the current namespace (or an outer one)
-- that is: the namespace of 'n' is a parent of nspace
export
visibleIn : Namespace -> Name -> Visibility -> Bool
visibleIn nspace (NS ns n) Private = isParentOf ns nspace
-- Public and Export names are always visible
visibleIn nspace n _ = True

export
visibleInAny : List Namespace -> Name -> Visibility -> Bool
visibleInAny nss n vis = any (\ns => visibleIn ns n vis) nss

reducibleIn : Namespace -> Name -> Visibility -> Bool
reducibleIn nspace (NS ns (UN n)) Export = isParentOf ns nspace
reducibleIn nspace (NS ns (UN n)) Private = isParentOf ns nspace
reducibleIn nspace n _ = True

export
reducibleInAny : List Namespace -> Name -> Visibility -> Bool
reducibleInAny nss n vis = any (\ns => reducibleIn ns n vis) nss

export
toFullNames : {auto c : Ref Ctxt Defs} ->
              HasNames a => a -> Core a
toFullNames t
    = do defs <- get Ctxt
         full (gamma defs) t

export
toResolvedNames : {auto c : Ref Ctxt Defs} ->
                  HasNames a => a -> Core a
toResolvedNames t
    = do defs <- get Ctxt
         resolved (gamma defs) t

-- Make the name look nicer for user display
export
prettyName : {auto c : Ref Ctxt Defs} ->
             Name -> Core String
prettyName (Nested (i, _) n)
    = do i' <- toFullNames (Resolved i)
         pure (!(prettyName i') ++ "," ++
               !(prettyName n))
prettyName (CaseBlock outer idx)
    = pure ("case block in " ++ outer)
prettyName (WithBlock outer idx)
    = pure ("with block in " ++ outer)
prettyName (NS ns n) = prettyName n
prettyName n = pure (show n)

-- Add a hash of a thing that contains names,
-- but convert the internal numbers to full names first.
-- This makes the hash not depend on the internal numbering,
-- which is unstable.
export
addHashWithNames : {auto c : Ref Ctxt Defs} ->
  Hashable a => HasNames a => a -> Core ()
addHashWithNames x = toFullNames x >>= addHash

export
setFlag : {auto c : Ref Ctxt Defs} ->
        FC -> Name -> DefFlag -> Core ()
setFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         let flags' = fl :: filter (/= fl) (flags def)
         ignore $ addDef n ({ flags := flags' } def)

export
setNameFlag : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> DefFlag -> Core ()
setNameFlag fc n fl
    = do defs <- get Ctxt
         [(n', i, def)] <- lookupCtxtName n (gamma defs)
              | res => ambiguousName fc n (map fst res)
         let flags' = fl :: filter (/= fl) (flags def)
         ignore $ addDef (Resolved i) ({ flags := flags' } def)

export
unsetFlag : {auto c : Ref Ctxt Defs} ->
            FC -> Name -> DefFlag -> Core ()
unsetFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         let flags' = filter (/= fl) (flags def)
         ignore $ addDef n ({ flags := flags' } def)

export
hasFlag : {auto c : Ref Ctxt Defs} ->
          FC -> Name -> DefFlag -> Core Bool
hasFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         pure (fl `elem` flags def)

export
setSizeChange : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> List SCCall -> Core ()
setSizeChange loc n sc
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n ({ sizeChange := sc } def)

export
setTotality : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Totality -> Core ()
setTotality loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n ({ totality := tot } def)

export
setCovering : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Covering -> Core ()
setCovering loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n ({ totality->isCovering := tot } def)

export
setTerminating : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Terminating -> Core ()
setTerminating loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n ({ totality->isTerminating := tot } def)

export
getTotality : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Core Totality
getTotality loc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         pure $ totality def

export
getSizeChange : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core (List SCCall)
getSizeChange loc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         pure $ sizeChange def

export
setVisibility : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Visibility -> Core ()
setVisibility fc n vis
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         ignore $ addDef n ({ visibility := vis } def)

public export
record SearchData where
  constructor MkSearchData
  ||| determining argument positions
  detArgs : List Nat
  ||| Name of functions to use as hints, and whether ambiguity is allowed
  |||
  ||| In proof search, for every group of names
  |||  * If exactly one succeeds, use it
  |||  * If more than one succeeds, report an ambiguity error
  |||  * If none succeed, move on to the next group
  |||
  ||| This allows us to prioritise some names (e.g. to declare 'open' hints,
  ||| which we might us to open an implementation working as a module, or to
  ||| declare a named implementation to be used globally), and to have names
  ||| which are only used if all else fails (e.g. as a defaulting mechanism),
  ||| while the proof search mechanism doesn't need to know about any of the
  ||| details.
  hintGroups : List (Bool, List Name)

||| Get the auto search data for a name.
export
getSearchData : {auto c : Ref Ctxt Defs} ->
                FC -> (defaults : Bool) -> Name ->
                Core SearchData
getSearchData fc defaults target
    = do defs <- get Ctxt
         Just (TCon _ _ _ dets u _ _ _) <- lookupDefExact target (gamma defs)
              | _ => undefinedName fc target
         hs <- case lookup !(toFullNames target) (typeHints defs) of
                       Just hs => filterM (\x => notHidden x (gamma defs)) hs
                       Nothing => pure []
         if defaults
            then let defns = map fst !(filterM (\x => pure $ isDefault x
                                                 && !(notHidden x (gamma defs)))
                                             (toList (autoHints defs))) in
                     pure (MkSearchData [] [(False, defns)])
            else let opens = map fst !(filterM (\x => notHidden x (gamma defs))
                                             (toList (openHints defs)))
                     autos = map fst !(filterM (\x => pure $ not (isDefault x)
                                                 && !(notHidden x (gamma defs)))
                                             (toList (autoHints defs)))
                     tyhs = map fst (filter direct hs)
                     chasers = map fst (filter (not . direct) hs) in
                     pure (MkSearchData dets (filter (isCons . snd)
                               [(False, opens),
                                (False, autos),
                                (not (uniqueAuto u), tyhs),
                                (True, chasers)]))
  where
    ||| We don't want hidden (by `%hide`) names to appear in the search.
    ||| Lookup has to be done by a full qualified name, not a resolved ID.
    notHidden : forall a. (Name, a) -> Context -> Core Bool
    notHidden (n, _) ctxt = do
      fulln <- toFullNames n
      pure $ not (isHidden fulln ctxt)

    isDefault : (Name, Bool) -> Bool
    isDefault = snd

    direct : (Name, Bool) -> Bool
    direct = snd

export
setMutWith : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> List Name -> Core ()
setMutWith fc tn tns
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tn (gamma defs)
              | _ => undefinedName fc tn
         let TCon t a ps dets u _ cons det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setMutWith]"))
         updateDef tn (const (Just (TCon t a ps dets u tns cons det)))

export
addMutData : {auto c : Ref Ctxt Defs} ->
             Name -> Core ()
addMutData n = update Ctxt { mutData $= (n ::) }

export
dropMutData : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
dropMutData n = update Ctxt { mutData $= filter (/= n) }

export
setDetermining : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> List Name -> Core ()
setDetermining fc tyn args
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps _ u cons ms det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         apos <- getPos 0 args (type g)
         updateDef tyn (const (Just (TCon t a ps apos u cons ms det)))
  where
    -- Type isn't normalised, but the argument names refer to those given
    -- explicitly in the type, so there's no need.
    getPos : Nat -> List Name -> Term vs -> Core (List Nat)
    getPos i ns (Bind _ x (Pi _ _ _ _) sc)
        = if x `elem` ns
             then do rest <- getPos (1 + i) (filter (/=x) ns) sc
                     pure $ i :: rest
             else getPos (1 + i) ns sc
    getPos _ [] _ = pure []
    getPos _ ns ty = throw (GenericMsg fc ("Unknown determining arguments: "
                           ++ showSep ", " (map show ns)))

export
setDetags : {auto c : Ref Ctxt Defs} ->
            FC -> Name -> Maybe (List Nat) -> Core ()
setDetags fc tyn args
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps det u cons ms _ = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         updateDef tyn (const (Just (TCon t a ps det u cons ms args)))

export
setUniqueSearch : {auto c : Ref Ctxt Defs} ->
                  FC -> Name -> Bool -> Core ()
setUniqueSearch fc tyn u
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps ds fl cons ms det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         let fl' = { uniqueAuto := u } fl
         updateDef tyn (const (Just (TCon t a ps ds fl' cons ms det)))

export
setExternal : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Bool -> Core ()
setExternal fc tyn u
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps ds fl cons ms det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         let fl' = { external := u } fl
         updateDef tyn (const (Just (TCon t a ps ds fl' cons ms det)))

export
addHintFor : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Name -> Bool -> Bool -> Core ()
addHintFor fc tyn_in hintn_in direct loading
    = do defs <- get Ctxt
         tyn <- toFullNames tyn_in
          -- ^ We have to index by full name because of the order we load -
          -- the name may not be resolved yet when we load the hints.
          -- Revisit if this turns out to be a bottleneck (it seems unlikely)
         hintn <- toResolvedNames hintn_in

         let hs = case lookup tyn (typeHints defs) of
                       Just hs => hs
                       Nothing => []
         if loading
            then put Ctxt
                     ({ typeHints $= insert tyn ((hintn, direct) :: hs)
                      } defs)
            else put Ctxt
                     ({ typeHints $= insert tyn ((hintn, direct) :: hs),
                        saveTypeHints $= ((tyn, hintn, direct) :: )
                      } defs)

export
addGlobalHint : {auto c : Ref Ctxt Defs} ->
                Name -> Bool -> Core ()
addGlobalHint hintn_in isdef
    = do hintn <- toResolvedNames hintn_in
         update Ctxt { autoHints $= insert hintn isdef,
                       saveAutoHints $= ((hintn, isdef) ::) }

export
addLocalHint : {auto c : Ref Ctxt Defs} ->
               Name -> Core ()
addLocalHint hintn_in
    = do hintn <- toResolvedNames hintn_in
         update Ctxt { localHints $= insert hintn () }

export
addOpenHint : {auto c : Ref Ctxt Defs} -> Name -> Core ()
addOpenHint hintn_in
    = do hintn <- toResolvedNames hintn_in
         update Ctxt { openHints $= insert hintn () }

export
dropOpenHint : {auto c : Ref Ctxt Defs} -> Name -> Core ()
dropOpenHint hintn_in
    = do hintn <- toResolvedNames hintn_in
         update Ctxt { openHints $= delete hintn }

export
setOpenHints : {auto c : Ref Ctxt Defs} -> NameMap () -> Core ()
setOpenHints hs = update Ctxt { openHints := hs }

export
addTransform : {auto c : Ref Ctxt Defs} ->
               FC -> Transform -> Core ()
addTransform fc t_in
    = do defs <- get Ctxt
         let Just fn_in = getFnName t_in
             | Nothing =>
                  throw (GenericMsg fc "LHS of a transformation must be a function application")
         fn <- toResolvedNames fn_in
         t <- toResolvedNames t_in
         fn_full <- toFullNames fn_in
         t_full <- toFullNames t_in
         case lookup fn (transforms defs) of
              Nothing =>
                 put Ctxt ({ transforms $= insert fn [t],
                             saveTransforms $= ((fn_full, t_full) ::) } defs)
              Just ts =>
                 put Ctxt ({ transforms $= insert fn (t :: ts),
                             saveTransforms $= ((fn_full, t_full) ::) } defs)

export
clearSavedHints : {auto c : Ref Ctxt Defs} -> Core ()
clearSavedHints = update Ctxt { saveTypeHints := [], saveAutoHints := [] }

-- Set the default namespace for new definitions
export
setNS : {auto c : Ref Ctxt Defs} -> Namespace -> Core ()
setNS ns = update Ctxt { currentNS := ns }

-- Set the nested namespaces we're allowed to look inside
export
setNestedNS : {auto c : Ref Ctxt Defs} ->
              List Namespace -> Core ()
setNestedNS ns = update Ctxt { nestedNS := ns }

-- Get the default namespace for new definitions
export
getNS : {auto c : Ref Ctxt Defs} ->
        Core Namespace
getNS
    = do defs <- get Ctxt
         pure (currentNS defs)

-- Get the nested namespaces we're allowed to look inside
export
getNestedNS : {auto c : Ref Ctxt Defs} ->
              Core (List Namespace)
getNestedNS
    = do defs <- get Ctxt
         pure (nestedNS defs)

-- Add the module name, and namespace, of an imported module
-- (i.e. for "import X as Y", it's (X, Y)
-- "import public X" is, when rexported, the same as
-- "import X as [current namespace]")
export
addImported : {auto c : Ref Ctxt Defs} ->
              (ModuleIdent, Bool, Namespace) -> Core ()
addImported mod = update Ctxt { imported $= (mod ::) }

export
getImported : {auto c : Ref Ctxt Defs} ->
              Core (List (ModuleIdent, Bool, Namespace))
getImported
    = do defs <- get Ctxt
         pure (imported defs)

export
addDirective : {auto c : Ref Ctxt Defs} ->
               String -> String -> Core ()
addDirective c str
    = do defs <- get Ctxt
         case getCG (options defs) c of
              Nothing => -- warn, rather than fail, because the CG may exist
                         -- but be unknown to this particular instance
                         coreLift $ putStrLn $ "Unknown code generator " ++ c
              Just cg => put Ctxt ({ cgdirectives $= ((cg, str) ::) } defs)

export
getDirectives : {auto c : Ref Ctxt Defs} ->
                CG -> Core (List String)
getDirectives cg
    = do defs <- get Ctxt
         pure $ defs.options.session.directives ++
                 mapMaybe getDir (cgdirectives defs)
  where
    getDir : (CG, String) -> Maybe String
    getDir (x', str) = if cg == x' then Just str else Nothing

export
getNextTypeTag : {auto c : Ref Ctxt Defs} ->
                 Core Int
getNextTypeTag
    = do defs <- get Ctxt
         put Ctxt ({ nextTag $= (+1) } defs)
         pure (nextTag defs)

-- Add a new nested namespace to the current namespace for new definitions
-- e.g. extendNS ["Data"] when namespace is "Prelude.List" leads to
-- current namespace of "Prelude.List.Data"
-- Inner namespaces go first, for ease of name lookup
export
extendNS : {auto c : Ref Ctxt Defs} -> Namespace -> Core ()
extendNS ns = update Ctxt { currentNS $= (<.> ns) }

export
withExtendedNS : {auto c : Ref Ctxt Defs} ->
                 Namespace -> Core a -> Core a
withExtendedNS ns act
    = do defs <- get Ctxt
         let cns = currentNS defs
         put Ctxt ({ currentNS := cns <.> ns } defs)
         ma <- catch (Right <$> act) (pure . Left)
         defs <- get Ctxt
         put Ctxt ({ currentNS := cns } defs)
         case ma of
           Left err => throw err
           Right a  => pure a

-- Get the name as it would be defined in the current namespace
-- i.e. if it doesn't have an explicit namespace already, add it,
-- otherwise leave it alone
export
inCurrentNS : {auto c : Ref Ctxt Defs} ->
              Name -> Core Name
inCurrentNS (UN n)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) (UN n))
inCurrentNS n@(CaseBlock _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(WithBlock _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(Nested _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(MN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(DN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n = pure n

export
setVisible : {auto c : Ref Ctxt Defs} ->
             Namespace -> Core ()
setVisible nspace = update Ctxt { gamma->visibleNS $= (nspace ::) }

export
getVisible : {auto c : Ref Ctxt Defs} ->
             Core (List Namespace)
getVisible
    = do defs <- get Ctxt
         pure (visibleNS (gamma defs))

-- set whether all names should be viewed as public. Be careful with this,
-- it's not intended for when checking user code! It's meant for allowing
-- easy checking of partially evaluated definitions.
export
setAllPublic : {auto c : Ref Ctxt Defs} ->
               (pub : Bool) -> Core ()
setAllPublic pub = update Ctxt { gamma->allPublic := pub }

export
isAllPublic : {auto c : Ref Ctxt Defs} ->
              Core Bool
isAllPublic
    = do defs <- get Ctxt
         pure (allPublic (gamma defs))

-- Return True if the given namespace is visible in the context (meaning
-- the namespace itself, and any namespace it's nested inside)
export
isVisible : {auto c : Ref Ctxt Defs} ->
            Namespace -> Core Bool
isVisible nspace
    = do defs <- get Ctxt
         pure (any visible (allParents (currentNS defs) ++
                            nestedNS defs ++
                            visibleNS (gamma defs)))

  where
    -- Visible if any visible namespace is a parent of the namespace we're
    -- asking about
    visible : Namespace -> Bool
    visible visns = isParentOf visns nspace

-- Get the next entry id in the context (this is for recording where to go
-- back to when backtracking in the elaborator)
export
getNextEntry : {auto c : Ref Ctxt Defs} ->
               Core Int
getNextEntry
    = do defs <- get Ctxt
         pure (nextEntry (gamma defs))

export
setNextEntry : {auto c : Ref Ctxt Defs} ->
               Int -> Core ()
setNextEntry i = update Ctxt { gamma->nextEntry := i }

-- Set the 'first entry' index (i.e. the first entry in the current file)
-- to the place we currently are in the context
export
resetFirstEntry : {auto c : Ref Ctxt Defs} ->
                  Core ()
resetFirstEntry
    = do defs <- get Ctxt
         put Ctxt ({ gamma->firstEntry := nextEntry (gamma defs) } defs)

export
getFullName : {auto c : Ref Ctxt Defs} ->
              Name -> Core Name
getFullName (Resolved i)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure (Resolved i)
         pure (fullname gdef)
getFullName n = pure n

-- Getting and setting various options

export
getPPrint : {auto c : Ref Ctxt Defs} ->
            Core PPrinter
getPPrint
    = do defs <- get Ctxt
         pure (printing (options defs))

export
setPPrint : {auto c : Ref Ctxt Defs} -> PPrinter -> Core ()
setPPrint ppopts = update Ctxt { options->printing := ppopts }

export
setCG : {auto c : Ref Ctxt Defs} -> CG -> Core ()
setCG cg = update Ctxt { options->session->codegen := cg }

export
getDirs : {auto c : Ref Ctxt Defs} -> Core Dirs
getDirs
    = do defs <- get Ctxt
         pure (dirs (options defs))

export
addExtraDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addExtraDir dir = update Ctxt { options->dirs->extra_dirs $= (++ [dir]) }

export
addPackageDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addPackageDir dir = update Ctxt { options->dirs->package_dirs $= (++ [dir]) }

export
addDataDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addDataDir dir = update Ctxt { options->dirs->data_dirs $= (++ [dir]) }

export
addLibDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addLibDir dir = update Ctxt { options->dirs->lib_dirs $= (++ [dir]) }

export
setBuildDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setBuildDir dir = update Ctxt { options->dirs->build_dir := dir }

export
setDependsDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setDependsDir dir = update Ctxt { options->dirs->depends_dir := dir }

export
setOutputDir : {auto c : Ref Ctxt Defs} -> Maybe String -> Core ()
setOutputDir dir = update Ctxt { options->dirs->output_dir := dir }

export
setSourceDir : {auto c : Ref Ctxt Defs} -> Maybe String -> Core ()
setSourceDir mdir = update Ctxt { options->dirs->source_dir := mdir }

export
setWorkingDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setWorkingDir dir
    = do coreLift_ $ changeDir dir
         Just cdir <- coreLift $ currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         update Ctxt { options->dirs->working_dir := cdir }

export
getWorkingDir : Core String
getWorkingDir
    = do Just d <- coreLift $ currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         pure d

export
withCtxt : {auto c : Ref Ctxt Defs} -> Core a -> Core a
withCtxt = wrapRef Ctxt resetCtxt
  where
    resetCtxt : Defs -> Core ()
    resetCtxt defs = do let dir = defs.options.dirs.working_dir
                        coreLift_ $ changeDir dir

export
setPrefix : {auto c : Ref Ctxt Defs} -> String -> Core ()
setPrefix dir = update Ctxt { options->dirs->prefix_dir := dir }

export
setExtension : {auto c : Ref Ctxt Defs} -> LangExt -> Core ()
setExtension e = update Ctxt { options $= setExtension e }

export
isExtension : LangExt -> Defs -> Bool
isExtension e defs = isExtension e (options defs)

export
checkUnambig : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Core Name
checkUnambig fc n
    = do defs <- get Ctxt
         case !(lookupDefName n (gamma defs)) of
              [(fulln, i, _)] => pure (Resolved i)
              ns => ambiguousName fc n (map fst ns)

export
lazyActive : {auto c : Ref Ctxt Defs} -> Bool -> Core ()
lazyActive a = update Ctxt { options->elabDirectives->lazyActive := a }

export
setUnboundImplicits : {auto c : Ref Ctxt Defs} -> Bool -> Core ()
setUnboundImplicits a = update Ctxt { options->elabDirectives->unboundImplicits := a }

export
setPrefixRecordProjections : {auto c : Ref Ctxt Defs} -> Bool -> Core ()
setPrefixRecordProjections b = update Ctxt { options->elabDirectives->prefixRecordProjections := b }

export
setDefaultTotalityOption : {auto c : Ref Ctxt Defs} ->
                           TotalReq -> Core ()
setDefaultTotalityOption tot = update Ctxt { options->elabDirectives->totality := tot }

export
setAmbigLimit : {auto c : Ref Ctxt Defs} ->
                Nat -> Core ()
setAmbigLimit max = update Ctxt { options->elabDirectives->ambigLimit := max }

export
setAutoImplicitLimit : {auto c : Ref Ctxt Defs} ->
                       Nat -> Core ()
setAutoImplicitLimit max = update Ctxt { options->elabDirectives->autoImplicitLimit := max }

export
setNFThreshold : {auto c : Ref Ctxt Defs} ->
                 Nat -> Core ()
setNFThreshold max = update Ctxt { options->elabDirectives->nfThreshold := max }

export
setSearchTimeout : {auto c : Ref Ctxt Defs} ->
                   Integer -> Core ()
setSearchTimeout t = update Ctxt { options->session->searchTimeout := t }

export
isLazyActive : {auto c : Ref Ctxt Defs} ->
               Core Bool
isLazyActive
    = do defs <- get Ctxt
         pure (lazyActive (elabDirectives (options defs)))

export
isUnboundImplicits : {auto c : Ref Ctxt Defs} ->
                  Core Bool
isUnboundImplicits
    = do defs <- get Ctxt
         pure (unboundImplicits (elabDirectives (options defs)))

export
isPrefixRecordProjections : {auto c : Ref Ctxt Defs} -> Core Bool
isPrefixRecordProjections =
  prefixRecordProjections . elabDirectives . options <$> get Ctxt

export
getDefaultTotalityOption : {auto c : Ref Ctxt Defs} ->
                           Core TotalReq
getDefaultTotalityOption
    = do defs <- get Ctxt
         pure (totality (elabDirectives (options defs)))

export
getAmbigLimit : {auto c : Ref Ctxt Defs} ->
                Core Nat
getAmbigLimit
    = do defs <- get Ctxt
         pure (ambigLimit (elabDirectives (options defs)))

export
getAutoImplicitLimit : {auto c : Ref Ctxt Defs} ->
                       Core Nat
getAutoImplicitLimit
    = do defs <- get Ctxt
         pure (autoImplicitLimit (elabDirectives (options defs)))

export
setPair : {auto c : Ref Ctxt Defs} ->
          FC -> (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Core ()
setPair fc ty f s
    = do ty' <- checkUnambig fc ty
         f' <- checkUnambig fc f
         s' <- checkUnambig fc s
         update Ctxt { options $= setPair ty' f' s' }

export
setRewrite : {auto c : Ref Ctxt Defs} ->
             FC -> (eq : Name) -> (rwlemma : Name) -> Core ()
setRewrite fc eq rw
    = do rw' <- checkUnambig fc rw
         eq' <- checkUnambig fc eq
         update Ctxt { options $= setRewrite eq' rw' }

-- Don't check for ambiguity here; they're all meant to be overloadable
export
setFromInteger : {auto c : Ref Ctxt Defs} ->
                 Name -> Core ()
setFromInteger n = update Ctxt { options $= setFromInteger n }

export
setFromString : {auto c : Ref Ctxt Defs} ->
                Name -> Core ()
setFromString n = update Ctxt { options $= setFromString n }

export
setFromChar : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
setFromChar n = update Ctxt { options $= setFromChar n }

export
setFromDouble : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
setFromDouble n = update Ctxt { options $= setFromDouble n }

export
addNameDirective : {auto c : Ref Ctxt Defs} ->
                   FC -> Name -> List String -> Core ()
addNameDirective fc n ns
    = do n' <- checkUnambig fc n
         update Ctxt { namedirectives $= insert n' ns  }

-- Checking special names from Options

export
isPairType : {auto c : Ref Ctxt Defs} ->
             Name -> Core Bool
isPairType n
    = do defs <- get Ctxt
         case pairnames (options defs) of
              Nothing => pure False
              Just l => pure $ !(getFullName n) == !(getFullName (pairType l))

export
fstName : {auto c : Ref Ctxt Defs} ->
          Core (Maybe Name)
fstName
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . fstName) (pairnames (options defs))

export
sndName : {auto c : Ref Ctxt Defs} ->
          Core (Maybe Name)
sndName
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . sndName) (pairnames (options defs))

export
getRewrite :{auto c : Ref Ctxt Defs} ->
            Core (Maybe Name)
getRewrite
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . rewriteName) (rewritenames (options defs))

export
isEqualTy : {auto c : Ref Ctxt Defs} ->
            Name -> Core Bool
isEqualTy n
    = do defs <- get Ctxt
         case rewritenames (options defs) of
              Nothing => pure False
              Just r => pure $ !(getFullName n) == !(getFullName (equalType r))

export
fromIntegerName : {auto c : Ref Ctxt Defs} ->
                  Core (Maybe Name)
fromIntegerName
    = do defs <- get Ctxt
         pure $ fromIntegerName (primnames (options defs))

export
fromStringName : {auto c : Ref Ctxt Defs} ->
                 Core (Maybe Name)
fromStringName
    = do defs <- get Ctxt
         pure $ fromStringName (primnames (options defs))

export
fromCharName : {auto c : Ref Ctxt Defs} ->
               Core (Maybe Name)
fromCharName
    = do defs <- get Ctxt
         pure $ fromCharName (primnames (options defs))

export
fromDoubleName : {auto c : Ref Ctxt Defs} ->
               Core (Maybe Name)
fromDoubleName
    = do defs <- get Ctxt
         pure $ fromDoubleName (primnames (options defs))

export
getPrimNames : {auto c : Ref Ctxt Defs} -> Core PrimNames
getPrimNames = [| MkPrimNs fromIntegerName fromStringName fromCharName fromDoubleName |]

export
getPrimitiveNames : {auto c : Ref Ctxt Defs} -> Core (List Name)
getPrimitiveNames = primNamesToList <$> getPrimNames

export
isPrimName : List Name -> Name -> Bool
isPrimName prims given = let (ns, nm) = splitNS given in go ns nm prims where

  go : Namespace -> Name -> List Name -> Bool
  go ns nm [] = False
  go ns nm (p :: ps)
    = let (ns', nm') = splitNS p in
      (nm' == nm && (ns' `isApproximationOf` ns))
      || go ns nm ps

export
addLogLevel : {auto c : Ref Ctxt Defs} ->
              Maybe LogLevel -> Core ()
addLogLevel Nothing  = update Ctxt { options->session->logEnabled := False, options->session->logLevel := defaultLogLevel }
addLogLevel (Just l) = update Ctxt { options->session->logEnabled := True, options->session->logLevel $= insertLogLevel l }

export
withLogLevel : {auto c : Ref Ctxt Defs} ->
               LogLevel -> Core a -> Core a
withLogLevel l comp = do
  defs <- get Ctxt
  let logs = logLevel (session (options defs))
  put Ctxt ({ options->session->logLevel := insertLogLevel l logs } defs)
  r <- comp
  defs <- get Ctxt
  put Ctxt ({ options->session->logLevel := logs } defs)
  pure r

export
setLogTimings : {auto c : Ref Ctxt Defs} -> Nat -> Core ()
setLogTimings n = update Ctxt { options->session->logTimings := Just n }

export
setDebugElabCheck : {auto c : Ref Ctxt Defs} -> Bool -> Core ()
setDebugElabCheck b = update Ctxt { options->session->debugElabCheck := b }

export
getSession : {auto c : Ref Ctxt Defs} ->
             Core Session
getSession
    = do defs <- get Ctxt
         pure (session (options defs))

export
setSession : {auto c : Ref Ctxt Defs} -> Session -> Core ()
setSession sopts = update Ctxt { options->session := sopts }

%inline
export
updateSession : {auto c : Ref Ctxt Defs} ->
                (Session -> Session) -> Core ()
updateSession f = setSession (f !getSession)

export
recordWarning : {auto c : Ref Ctxt Defs} -> Warning -> Core ()
recordWarning w = update Ctxt { warnings $= (w ::) }

export
getTime : Core Integer
getTime
    = do clock <- coreLift (clockTime Monotonic)
         pure (seconds clock * nano + nanoseconds clock)
  where
    nano : Integer
    nano = 1000000000

-- A simple timeout mechanism. We can start a timer, clear it, or check
-- whether too much time has passed and throw an exception if so

||| Initialise the timer, setting the time in milliseconds after which a
||| timeout should be thrown.
||| Note: It's important to clear the timer when the operation that might
||| timeout is complete, otherwise something else might throw a timeout
||| error!
export
startTimer : {auto c : Ref Ctxt Defs} ->
             Integer -> String -> Core ()
startTimer tmax action
    = do t <- getTime
         update Ctxt { timer := Just (t + tmax * 1000000, action) }

||| Clear the timer
export
clearTimer : {auto c : Ref Ctxt Defs} -> Core ()
clearTimer = update Ctxt { timer := Nothing }

||| If the timer was started more than t milliseconds ago, throw an exception
export
checkTimer : {auto c : Ref Ctxt Defs} ->
             Core ()
checkTimer
    = do defs <- get Ctxt
         let Just (max, action) = timer defs
                | Nothing => pure ()
         t <- getTime
         if (t > max)
            then throw (Timeout action)
            else pure ()

-- Update the list of imported incremental compile data, if we're in
-- incremental mode for the current CG
export
addImportedInc : {auto c : Ref Ctxt Defs} ->
                 ModuleIdent -> List (CG, String, List String) -> Core ()
addImportedInc modNS inc
    = do s <- getSession
         let cg = s.codegen
         defs <- get Ctxt
         when (cg `elem` s.incrementalCGs) $
           case lookup cg inc of
                Nothing =>
                  -- No incremental compile data for current CG, so we can't
                  -- compile incrementally
                  do recordWarning (GenericWarn ("No incremental compile data for " ++ show modNS))
                     defs <- get Ctxt
                     put Ctxt ({ allIncData $= drop cg } defs)
                     -- Tell session that the codegen is no longer incremental
                     when (show modNS /= "") $
                        updateSession { incrementalCGs $= (delete cg) }
                Just (mods, extra) =>
                     put Ctxt ({ allIncData $= addMod cg (mods, extra) }
                                      defs)
  where
    addMod : CG -> (String, List String) ->
             List (CG, (List String, List String)) ->
             List (CG, (List String, List String))
    addMod cg (mod, all) [] = [(cg, ([mod], all))]
    addMod cg (mod, all) ((cg', (mods, libs)) :: xs)
        = if cg == cg'
             then ((cg, (mod :: mods, libs ++ all)) :: xs)
             else ((cg', (mods, libs)) :: addMod cg (mod, all) xs)

    drop : CG -> List (CG, a) -> List (CG, a)
    drop cg [] = []
    drop cg ((x, v) :: xs)
        = if cg == x
             then xs
             else ((x, v) :: drop cg xs)

export
setIncData : {auto c : Ref Ctxt Defs} ->
             CG -> (String, List String) -> Core ()
setIncData cg res = update Ctxt { incData $= ((cg, res) :: )}

-- Set a name as Private that was previously visible (and, if 'everywhere' is
-- set, hide in any modules imported by this one)
export
hide : {auto c : Ref Ctxt Defs} ->
       FC -> Name -> Core ()
hide fc n
    = do defs <- get Ctxt
         [(nsn, _)] <- lookupCtxtName n (gamma defs)
              | res => ambiguousName fc n (map fst res)
         put Ctxt ({ gamma $= hideName nsn } defs)

-- Set a name as Public that was previously hidden
-- Note: this is here at the bottom only becuase `recordWarning` is defined just above.
export
unhide : {auto c : Ref Ctxt Defs} ->
       FC -> Name -> Core ()
unhide fc n
    = do defs <- get Ctxt
         [(nsn, _)] <- lookupHiddenCtxtName n (gamma defs)
              | res => ambiguousName fc n (map fst res)
         put Ctxt ({ gamma $= unhideName nsn } defs)
         unless (isHidden nsn (gamma defs)) $ do
           recordWarning $ GenericWarn $
             "Trying to %unhide `" ++ show nsn ++ "`, which was not hidden in the first place"
