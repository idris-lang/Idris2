module Core.Name.Scoped

import Core.Name
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

%default total

------------------------------------------------------------------------
-- Basic type definitions

public export
Scope : Type
Scope = SnocList Name

public export
Scoped : Type
Scoped = Scope -> Type

------------------------------------------------------------------------
-- Compatible variables

public export
data CompatibleVars : SnocList a -> SnocList a -> Type where
   Pre : CompatibleVars xs xs
   Ext : CompatibleVars xs ys -> CompatibleVars (xs :< n) (ys :< m)

export
invertExt : CompatibleVars (xs :< n) (ys :< m) -> CompatibleVars xs ys
invertExt Pre = Pre
invertExt (Ext p) = p

export
extendCompats : (args : SnocList a) ->
                CompatibleVars xs ys ->
                CompatibleVars (xs ++ args) (ys ++ args)
extendCompats [<] prf = prf
extendCompats (xs :< x) prf = Ext (extendCompats xs prf)

export
decCompatibleVars : (xs, ys : SnocList a) -> Dec (CompatibleVars xs ys)
decCompatibleVars [<] [<] = Yes Pre
decCompatibleVars [<] (sx :< x) = No (\case p impossible)
decCompatibleVars (sx :< x) [<] = No (\case p impossible)
decCompatibleVars (sx :< x) (sy :< y) = case decCompatibleVars sx sy of
  Yes prf => Yes (Ext prf)
  No nprf => No (nprf . invertExt)

export
areCompatibleVars : (xs : SnocList a) -> (ys : SnocList a) ->
                    Maybe (CompatibleVars xs ys)
areCompatibleVars [<] [<] = pure Pre
areCompatibleVars (xs :< x) (ys :< y)
    = do compat <- areCompatibleVars xs ys
         pure (Ext compat)
areCompatibleVars _ _ = Nothing

------------------------------------------------------------------------
-- Thinnings

public export
data Thin : SnocList a -> SnocList a -> Type where
  Refl : Thin xs xs
  Drop : Thin xs ys -> Thin xs (ys :< y)
  Keep : Thin xs ys -> Thin (xs :< x) (ys :< y)

||| Smart constructor. We should use this to maximise the length
||| of the Refl segment thus getting more short-circuiting behaviours
export
keep : Thin xs ys -> Thin (xs :< x) (ys :< x)
keep Refl = Refl
keep p = Keep p

export
keeps : (args : SnocList a) -> Thin xs ys -> Thin (xs ++ args) (ys ++ args)
keeps [<] th = th
keeps (sx :< x) th = keep (keeps sx th)

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
  weaken : tm vars -> tm (vars :< nm)
  weakenNs : Weakenable tm

  -- default implementations
  weakenNs p t = case sizedView p of
    Z   => t
    S p => weaken (weakenNs p t)

  weaken = weakenNs (suc zero)

public export
interface Strengthen (0 tm : Scoped) where
  constructor MkStrengthen
  -- methods
  strengthen : tm (vars :< nm) -> Maybe (tm vars)
  strengthenNs : Strengthenable tm

  -- default implementations
  strengthenNs p t = case sizedView p of
    Z   => pure t
    S p' => strengthenNs p' =<< strengthen t

  strengthen = strengthenNs (suc zero)

public export
interface FreelyEmbeddable (0 tm : Scoped) where
  constructor MkFreelyEmbeddable
  -- this is free for nameless representations
  embed : Embeddable tm
  embed = believe_me

export
ListFreelyEmbeddable : FreelyEmbeddable tm => FreelyEmbeddable (List . tm)
ListFreelyEmbeddable = MkFreelyEmbeddable believe_me

public export
interface Weaken tm => IsScoped (0 tm : Scoped) where
  -- methods
  compat : tm (xs :< m) -> tm (xs :< n)
  compatNs : CompatibleVars xs ys -> tm xs -> tm ys

  thin : Thinnable tm
  shrink : Shrinkable tm

  -- default implementations
  compat = compatNs (Ext Pre)
