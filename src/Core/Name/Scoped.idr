module Core.Name.Scoped

import Core.Name

import public Data.List.HasLength
import Data.SnocList

import public Libraries.Data.List.SizeOf

%default total

------------------------------------------------------------------------
-- Basic type definitions

||| A scope is represented by a list of names. E.g. in the following
||| rule, the scope Γ is extended with x when going under the λx.
||| binder:
|||
|||    Γ, x ⊢ t : B
|||  -----------------------------
|||    Γ    ⊢ λx. t : A → B
public export
Scope : Type
Scope = SnocList Name

||| A scoped definition is one indexed by a scope
public export
Scoped : Type
Scoped = Scope -> Type

------------------------------------------------------------------------
-- Semi-decidable equality

export
scopeEq : (xs, ys : Scope) -> Maybe (xs = ys)
scopeEq [<] [<] = Just Refl
scopeEq (xs :< x) (ys :< y)
    = do Refl <- nameEq x y
         Refl <- scopeEq xs ys
         Just Refl
scopeEq _ _ = Nothing

------------------------------------------------------------------------
-- Generate a fresh name (for a given scope)

export
mkFresh : Scope -> Name -> Name
mkFresh vs n
  = if n `elem` vs
    then assert_total $ mkFresh vs (next n)
    else n

------------------------------------------------------------------------
-- Concepts

public export
0 Weakenable : Scoped -> Type
Weakenable tm = {0 vars, ns : Scope} ->
  SizeOf ns -> tm vars -> tm (vars ++ ns)

public export
0 Strengthenable : Scoped -> Type
Strengthenable tm = {0 vars, ns : Scope} ->
  SizeOf ns -> tm (vars ++ ns) -> Maybe (tm vars)

public export
0 GenWeakenable : Scoped -> Type
GenWeakenable tm = {0 outer, ns, local : Scope} ->
  SizeOf local -> SizeOf ns -> tm (outer ++ local) -> tm ((outer ++ ns) ++ local)

public export
0 Thinnable : Scoped -> Type
Thinnable tm = {0 xs, ys : Scope} -> tm xs -> Thin xs ys -> tm ys

public export
0 Shrinkable : Scoped -> Type
Shrinkable tm = {0 xs, ys : Scope} -> tm xs -> Thin ys xs -> Maybe (tm ys)

public export
0 Embeddable : Scoped -> Type
Embeddable tm = {0 outer, vars : Scope} -> tm vars -> tm (outer ++ vars)

------------------------------------------------------------------------
-- IsScoped interface

public export
interface Weaken (0 tm : Scoped) where
  constructor MkWeaken
  -- methods
  weaken : tm vars -> tm (nm :%: vars)
  weakenNs : Weakenable tm
  -- default implementations
  weaken = weakenNs (suc zero)

-- This cannot be merged with Weaken because of WkCExp
public export
interface GenWeaken (0 tm : Scoped) where
  constructor MkGenWeaken
  genWeakenNs : GenWeakenable tm

export
genWeaken : GenWeaken tm =>
  SizeOf local -> tm (outer ++ local) -> tm (local +%+ n :%: outer)
genWeaken l = genWeakenNs l (suc zero)

public export
interface Strengthen (0 tm : Scoped) where
  constructor MkStrengthen
  -- methods
  strengthenNs : Strengthenable tm

export
strengthen : Strengthen tm => tm (nm :%: vars) -> Maybe (tm vars)
strengthen = strengthenNs (suc zero)

public export
interface FreelyEmbeddable (0 tm : Scoped) where
  constructor MkFreelyEmbeddable
  -- this is free for nameless representations
  embed : Embeddable tm
  embed = believe_me

export
FunctorFreelyEmbeddable : Functor f => FreelyEmbeddable tm => FreelyEmbeddable (f . tm)
FunctorFreelyEmbeddable = MkFreelyEmbeddable believe_me

export
ListFreelyEmbeddable : FreelyEmbeddable tm => FreelyEmbeddable (List . tm)
ListFreelyEmbeddable = FunctorFreelyEmbeddable

export
MaybeFreelyEmbeddable : FreelyEmbeddable tm => FreelyEmbeddable (Maybe . tm)
MaybeFreelyEmbeddable = FunctorFreelyEmbeddable

export
GenWeakenWeakens : GenWeaken tm => Weaken tm
GenWeakenWeakens = MkWeaken (genWeakenNs zero (suc zero)) (genWeakenNs zero)

export
FunctorGenWeaken : Functor f => GenWeaken tm => GenWeaken (f . tm)
FunctorGenWeaken = MkGenWeaken (\ l, s => map (genWeakenNs l s))

export
FunctorWeaken : Functor f => Weaken tm => Weaken (f . tm)
FunctorWeaken = MkWeaken (go (suc zero)) go where

  go : Weakenable (f . tm)
  go s = map (weakenNs s)

export
ListWeaken : Weaken tm => Weaken (List . tm)
ListWeaken = FunctorWeaken

export
MaybeWeaken : Weaken tm => Weaken (Maybe . tm)
MaybeWeaken = FunctorWeaken

public export
interface Weaken tm => IsScoped (0 tm : Scoped) where
  -- methods
  compatNs : CompatibleVars xs ys -> tm xs -> tm ys

  thin : Thinnable tm
  shrink : Shrinkable tm

export
compat : IsScoped tm => tm (m :%: xs) -> tm (n :%: xs)
compat = compatNs (Ext Pre)
