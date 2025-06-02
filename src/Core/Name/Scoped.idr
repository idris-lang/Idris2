module Core.Name.Scoped

import public Core.Name
import Core.Name.CompatibleVars

import Data.SnocList

import public Libraries.Data.List.Thin
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.HasLength
import Libraries.Data.List.SizeOf

%default total

------------------------------------------------------------------------
-- Basic type definitions

||| Something which is having similar order as Scope itself
public export
Scopeable : (a: Type) -> Type
Scopeable = SnocList

||| A scope is represented by a list of names. E.g. in the following
||| rule, the scope Γ is extended with x when going under the λx.
||| binder:
|||
|||    Γ, x ⊢ t : B
|||  -----------------------------
|||    Γ    ⊢ λx. t : A → B
public export
Scope : Type
Scope = Scopeable Name

namespace Scope
  public export
  empty : Scopeable a
  empty = [<]

  public export
  ext : Scopeable a -> List a -> Scopeable a
  ext vars ns = vars <>< ns

  public export
  addInner : Scopeable a -> Scopeable a -> Scopeable a
  addInner vars inner = vars ++ inner

  public export
  bind : Scopeable a -> a -> Scopeable a
  bind vars n = vars :< n

  public export
  single : a -> Scopeable a
  single n = [<n]

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

export
localEq : (xs, ys : List Name) -> Maybe (xs = ys)
localEq [] [] = Just Refl
localEq (x :: xs) (y :: ys)
    = do Refl <- nameEq x y
         Refl <- localEq xs ys
         Just Refl
localEq _ _ = Nothing

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
  SizeOf ns -> tm vars -> tm (Scope.addInner vars ns)

public export
0 Strengthenable : Scoped -> Type
Strengthenable tm = {0 vars, ns : Scope} ->
  SizeOf ns -> tm (Scope.addInner vars ns) -> Maybe (tm vars)

public export
0 GenWeakenable : Scoped -> Type
GenWeakenable tm = {0 local, ns, outer : Scope} ->
  SizeOf outer -> SizeOf ns -> tm (Scope.addInner local outer) -> tm (Scope.addInner local (Scope.addInner ns outer))

public export
0 Thinnable : Scoped -> Type
Thinnable tm = {0 xs, ys : Scope} -> tm xs -> Thin xs ys -> tm ys

public export
0 Shrinkable : Scoped -> Type
Shrinkable tm = {0 xs, ys : Scope} -> tm xs -> Thin ys xs -> Maybe (tm ys)

public export
0 Embeddable : Scoped -> Type
Embeddable tm = {0 outer, vars : Scope} -> tm vars -> tm (Scope.addInner outer vars)

------------------------------------------------------------------------
-- IsScoped interface

public export
interface Weaken (0 tm : Scoped) where
  constructor MkWeaken
  -- methods
  weaken : tm vars -> tm (Scope.bind vars nm)
  weakenNs : Weakenable tm
  -- default implementations
  weaken = weakenNs (suc zero)
  weakenNs p t = case sizedView p of
    Z   => t
    S p => weaken (weakenNs p t)

-- This cannot be merged with Weaken because of WkCExp
public export
interface GenWeaken (0 tm : Scoped) where
  constructor MkGenWeaken
  genWeakenNs : GenWeakenable tm

export
genWeaken : GenWeaken tm =>
  SizeOf outer -> tm (Scope.addInner local outer) -> tm (Scope.addInner (Scope.bind local n) outer)
genWeaken l = rewrite sym $ appendAssociative local [<n] outer in genWeakenNs l (suc zero)

export
genWeakenFishily : GenWeaken tm =>
  SizeOf outer -> tm (Scope.ext local outer) -> tm (Scope.ext (Scope.bind local n) outer)
genWeakenFishily
    = rewrite fishAsSnocAppend local outer in
      rewrite fishAsSnocAppend (local :<n) outer in
      genWeaken . cast

export
weakensN : Weaken tm =>
  {0 vars : Scope} -> {0 ns : List Name} ->
  SizeOf ns -> tm vars -> tm (vars <>< ns)
weakensN s t
  = rewrite fishAsSnocAppend vars ns in
    weakenNs (zero <>< s) t

public export
interface Strengthen (0 tm : Scoped) where
  constructor MkStrengthen
  -- methods
  strengthenNs : Strengthenable tm

export
strengthen : Strengthen tm => tm (Scope.bind vars nm) -> Maybe (tm vars)
strengthen = strengthenNs (suc zero)

export
strengthensN :
  Strengthen tm => SizeOf ns ->
  tm (Scope.ext vars ns) -> Maybe (tm vars)
strengthensN s t
  = strengthenNs (zero <>< s)
  $ rewrite sym $ fishAsSnocAppend vars ns in t

public export
interface FreelyEmbeddable (0 tm : Scoped) where
  constructor MkFreelyEmbeddable
  -- this is free for nameless representations
  embed : Embeddable tm
  embed = believe_me

export
embedFishily : FreelyEmbeddable tm => tm (cast ns) -> tm (Scope.ext vars ns)
embedFishily t = rewrite fishAsSnocAppend vars ns in embed t

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
compat : IsScoped tm => tm (Scope.bind xs m) -> tm (Scope.bind xs n)
compat = compatNs (Ext Pre)
