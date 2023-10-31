module Core.TT

import public Core.FC
import public Core.Name
import public Core.Name.Scoped
import public Core.TT.Binder
import public Core.TT.Primitive
import public Core.TT.Var
import public Core.TT.Term

import Idris.Pretty.Annotations

import Data.String
import Data.Vect
import Decidable.Equality

import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Data.String.Extra

import public Algebra

import public Libraries.Data.SnocList.SizeOf

%default covering

------------------------------------------------------------------------
-- Kinded names (used for unelaboration and pretty printing)

public export
record KindedName where
  constructor MkKindedName
  nameKind : Maybe NameType
  fullName : Name -- fully qualified name
  rawName  : Name

%name KindedName kn

export
defaultKindedName : Name -> KindedName
defaultKindedName nm = MkKindedName Nothing nm nm

export
funKindedName : Name -> KindedName
funKindedName nm = MkKindedName (Just Func) nm nm

export
Show KindedName where show = show . rawName

export
covering
[Raw] Show KindedName where
  showPrec d (MkKindedName nm fn rn) =
    showCon d "MkKindedName" $ showArg nm ++ showArg @{Raw} fn ++ showArg @{Raw} rn


{-
namespace Bounds
  public export
  data Bounds : List Name -> Type where
       None : Bounds []
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

  export
  sizeOf : Bounds xs -> SizeOf xs
  sizeOf None        = zero
  sizeOf (Add _ _ b) = suc (sizeOf b)

export
addVars : SizeOf outer -> Bounds bound ->
          NVar name (outer ++ vars) ->
          NVar name (outer ++ (bound ++ vars))
addVars p = insertNVarNames p . sizeOf

resolveRef : SizeOf outer -> SizeOf done -> Bounds bound -> FC -> Name ->
             Maybe (Term (outer ++ (done ++ bound ++ vars)))
resolveRef p q None fc n = Nothing
resolveRef {outer} {done} p q (Add {xs} new old bs) fc n
    = if n == old
         then rewrite appendAssociative outer done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar (p + q) (MkNVar First) in
                     Just (Local fc Nothing _ p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef p (sucR q) bs fc n

mkLocals : SizeOf outer -> Bounds bound ->
           Term (outer ++ vars) -> Term (outer ++ (bound ++ vars))
mkLocals outer bs (Local fc r idx p)
    = let MkNVar p' = addVars outer bs (MkNVar p) in Local fc r _ p'
mkLocals outer bs (Ref fc Bound name)
    = maybe (Ref fc Bound name) id (resolveRef outer zero bs fc name)
mkLocals outer bs (Ref fc nt name)
    = Ref fc nt name
mkLocals outer bs (Meta fc name y xs)
    = maybe (Meta fc name y (map (mkLocals outer bs) xs))
            id (resolveRef outer zero bs fc name)
mkLocals outer bs (Bind fc x b scope)
    = Bind fc x (map (mkLocals outer bs) b)
           (mkLocals (suc outer) bs scope)
mkLocals outer bs (App fc fn arg)
    = App fc (mkLocals outer bs fn) (mkLocals outer bs arg)
mkLocals outer bs (As fc s as tm)
    = As fc s (mkLocals outer bs as) (mkLocals outer bs tm)
mkLocals outer bs (TDelayed fc x y)
    = TDelayed fc x (mkLocals outer bs y)
mkLocals outer bs (TDelay fc x t y)
    = TDelay fc x (mkLocals outer bs t) (mkLocals outer bs y)
mkLocals outer bs (TForce fc r x)
    = TForce fc r (mkLocals outer bs x)
mkLocals outer bs (PrimVal fc c) = PrimVal fc c
mkLocals outer bs (Erased fc Impossible) = Erased fc Impossible
mkLocals outer bs (Erased fc Placeholder) = Erased fc Placeholder
mkLocals outer bs (Erased fc (Dotted t)) = Erased fc (Dotted (mkLocals outer bs t))
mkLocals outer bs (TType fc u) = TType fc u

export
refsToLocals : Bounds bound -> Term vars -> Term (bound ++ vars)
refsToLocals None y = y
refsToLocals bs y = mkLocals zero  bs y

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm
-}

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  public export
  data SubstEnv : List Name -> List Name -> Type where
       Nil : SubstEnv [] vars
       (::) : Term vars ->
              SubstEnv ds vars -> SubstEnv (d :: ds) vars

  findDrop : FC -> Maybe Bool ->
             Var (dropped ++ vars) ->
             SubstEnv dropped vars ->
             Term vars
  findDrop fc r (MkVar var) [] = Local fc r _ var
  findDrop fc r (MkVar First) (tm :: env) = tm
  findDrop fc r (MkVar (Later p)) (tm :: env)
      = findDrop fc r (MkVar p) env

  find : FC -> Maybe Bool ->
         SizeOf outer ->
         Var (outer ++ (dropped ++ vars)) ->
         SubstEnv dropped vars ->
         Term (outer ++ vars)
  find fc r outer var env = case sizedView outer of
    Z       => findDrop fc r var env
    S outer => case var of
      MkVar First     => Local fc r _ First
      MkVar (Later p) => weaken (find fc r outer (MkVar p) env)
       -- TODO: refactor to only weaken once?

  substEnv : SizeOf outer ->
             SubstEnv dropped vars ->
             Term (outer ++ (dropped ++ vars)) ->
             Term (outer ++ vars)
  substEnv outer env (Local fc r _ prf)
      = find fc r outer (MkVar prf) env
  substEnv outer env (Ref fc x name) = Ref fc x name
  substEnv outer env (Meta fc n i xs)
      = Meta fc n i (map (substEnv outer env) xs)
  substEnv outer env (Bind fc x b scope)
      = Bind fc x (map (substEnv outer env) b)
                  (substEnv (suc outer) env scope)
  substEnv outer env (App fc fn arg)
      = App fc (substEnv outer env fn) (substEnv outer env arg)
  substEnv outer env (As fc s as pat)
      = As fc s (substEnv outer env as) (substEnv outer env pat)
  substEnv outer env (TDelayed fc x y) = TDelayed fc x (substEnv outer env y)
  substEnv outer env (TDelay fc x t y)
      = TDelay fc x (substEnv outer env t) (substEnv outer env y)
  substEnv outer env (TForce fc r x) = TForce fc r (substEnv outer env x)
  substEnv outer env (PrimVal fc c) = PrimVal fc c
  substEnv outer env (Erased fc Impossible) = Erased fc Impossible
  substEnv outer env (Erased fc Placeholder) = Erased fc Placeholder
  substEnv outer env (Erased fc (Dotted t)) = Erased fc (Dotted (substEnv outer env t))
  substEnv outer env (TType fc u) = TType fc u

  export
  substs : SubstEnv dropped vars -> Term (dropped ++ vars) -> Term vars
  substs env tm = substEnv zero env tm

  export
  subst : Term vars -> Term (x :: vars) -> Term vars
  subst val tm = substs [val] tm

-- Replace an explicit name with a term
export
substName : Name -> Term vars -> Term vars -> Term vars
substName x new (Ref fc nt name)
    = case nameEq x name of
           Nothing => Ref fc nt name
           Just Refl => new
substName x new (Meta fc n i xs)
    = Meta fc n i (map (substName x new) xs)
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName x new (Bind fc y b scope)
    = Bind fc y (map (substName x new) b) (substName x (weaken new) scope)
substName x new (App fc fn arg)
    = App fc (substName x new fn) (substName x new arg)
substName x new (As fc s as pat)
    = As fc s as (substName x new pat)
substName x new (TDelayed fc y z)
    = TDelayed fc y (substName x new z)
substName x new (TDelay fc y t z)
    = TDelay fc y (substName x new t) (substName x new z)
substName x new (TForce fc r y)
    = TForce fc r (substName x new y)
substName x new tm = tm

------------------------------------------------------------------------
-- Collecting info about terms

export
addMetas : (usingResolved : Bool) -> NameMap Bool -> Term vars -> NameMap Bool
addMetas res ns (Local fc x idx y) = ns
addMetas res ns (Ref fc x name) = ns
addMetas res ns (Meta fc n i xs)
  = addMetaArgs (insert (ifThenElse res (Resolved i) n) False ns) xs
  where
    addMetaArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
    addMetaArgs ns [] = ns
    addMetaArgs ns (t :: ts) = addMetaArgs (addMetas res ns t) ts
addMetas res ns (Bind fc x (Let _ c val ty) scope)
    = addMetas res (addMetas res (addMetas res ns val) ty) scope
addMetas res ns (Bind fc x b scope)
    = addMetas res (addMetas res ns (binderType b)) scope
addMetas res ns (App fc fn arg)
    = addMetas res (addMetas res ns fn) arg
addMetas res ns (As fc s as tm) = addMetas res ns tm
addMetas res ns (TDelayed fc x y) = addMetas res ns y
addMetas res ns (TDelay fc x t y)
    = addMetas res (addMetas res ns t) y
addMetas res ns (TForce fc r x) = addMetas res ns x
addMetas res ns (PrimVal fc c) = ns
addMetas res ns (Erased fc i) = foldr (flip $ addMetas res) ns i
addMetas res ns (TType fc u) = ns

-- Get the metavariable names in a term
export
getMetas : Term vars -> NameMap Bool
getMetas tm = addMetas False empty tm

export
addRefs : (underAssert : Bool) -> (aTotal : Name) ->
          NameMap Bool -> Term vars -> NameMap Bool
addRefs ua at ns (Local fc x idx y) = ns
addRefs ua at ns (Ref fc x name) = insert name ua ns
addRefs ua at ns (Meta fc n i xs)
    = addRefsArgs ns xs
  where
    addRefsArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
    addRefsArgs ns [] = ns
    addRefsArgs ns (t :: ts) = addRefsArgs (addRefs ua at ns t) ts
addRefs ua at ns (Bind fc x (Let _ c val ty) scope)
    = addRefs ua at (addRefs ua at (addRefs ua at ns val) ty) scope
addRefs ua at ns (Bind fc x b scope)
    = addRefs ua at (addRefs ua at ns (binderType b)) scope
addRefs ua at ns (App _ (App _ (Ref fc _ name) x) y)
    = if name == at
         then addRefs True at (insert name True ns) y
         else addRefs ua at (addRefs ua at (insert name ua ns) x) y
addRefs ua at ns (App fc fn arg)
    = addRefs ua at (addRefs ua at ns fn) arg
addRefs ua at ns (As fc s as tm) = addRefs ua at ns tm
addRefs ua at ns (TDelayed fc x y) = addRefs ua at ns y
addRefs ua at ns (TDelay fc x t y)
    = addRefs ua at (addRefs ua at ns t) y
addRefs ua at ns (TForce fc r x) = addRefs ua at ns x
addRefs ua at ns (PrimVal fc c) = ns
addRefs ua at ns (Erased fc i) = foldr (flip $ addRefs ua at) ns i
addRefs ua at ns (TType fc u) = ns

-- As above, but for references. Also flag whether a name is under an
-- 'assert_total' because we may need to know that in coverage/totality
-- checking
export
getRefs : (aTotal : Name) -> Term vars -> NameMap Bool
getRefs at tm = addRefs False at empty tm
