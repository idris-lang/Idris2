module Core.Name.Scoped

import Core.Name
import Core.Name.CompatibleVars

import Data.SnocList
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.List.SizeOf

%default total

------------------------------------------------------------------------
-- Basic type definitions

||| Something which is having similar order as Scope itself
public export
Scopeable : (a: Type) -> Type
Scopeable = List

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
  empty = []

  {-
  public export
  ext : Scopeable a -> List a -> Scopeable a
  ext vars ns = ns ++ vars
  --- TODO replace by `vars <>< ns`
  -}

  public export
  addInner : Scopeable a -> Scopeable a -> Scopeable a
  addInner vars inner = inner ++ vars
  --- TODO replace by `vars ++ inner`

  public export
  bind : Scopeable a -> a -> Scopeable a
  bind vars n = n :: vars
  --- TODO replace with `<:`

  public export
  single : a -> Scopeable a
  single n = [n]

||| A scoped definition is one indexed by a scope
public export
Scoped : Type
Scoped = Scope -> Type

------------------------------------------------------------------------
-- Semi-decidable equality

export
scopeEq : (xs, ys : Scope) -> Maybe (xs = ys)
scopeEq [] [] = Just Refl
scopeEq (x :: xs) (y :: ys)
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
-- Compatible variables

public export
data CompatibleVars : (xs, ys : List a) -> Type where
   Pre : CompatibleVars xs xs
   Ext : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
invertExt : CompatibleVars (n :: xs) (m :: ys) -> CompatibleVars xs ys
invertExt Pre = Pre
invertExt (Ext p) = p

export
extendCompats : (args : List a) ->
                CompatibleVars xs ys ->
                CompatibleVars (args ++ xs) (args ++ ys)
extendCompats args Pre = Pre
extendCompats args prf = go args prf where

  go : (args : List a) ->
       CompatibleVars xs ys ->
       CompatibleVars (args ++ xs) (args ++ ys)
  go [] prf = prf
  go (x :: xs) prf = Ext (go xs prf)

export
decCompatibleVars : (xs, ys : List a) -> Dec (CompatibleVars xs ys)
decCompatibleVars [] [] = Yes Pre
decCompatibleVars [] (x :: xs) = No (\case p impossible)
decCompatibleVars (x :: xs) [] = No (\case p impossible)
decCompatibleVars (x :: xs) (y :: ys) = case decCompatibleVars xs ys of
  Yes prf => Yes (Ext prf)
  No nprf => No (nprf . invertExt)

export
areCompatibleVars : (xs, ys : List a) ->
                    Maybe (CompatibleVars xs ys)
areCompatibleVars [] [] = pure Pre
areCompatibleVars (x :: xs) (y :: ys)
    = do compat <- areCompatibleVars xs ys
         pure (Ext compat)
areCompatibleVars _ _ = Nothing

------------------------------------------------------------------------
-- Thinnings

public export
data Thin : List a -> List a -> Type where
  Refl : Thin xs xs
  Drop : Thin xs ys -> Thin xs (y :: ys)
  Keep : Thin xs ys -> Thin (x :: xs) (x :: ys)

export
none : {xs : List a} -> Thin [] xs
none {xs = []} = Refl
none {xs = _ :: _} = Drop none

{- UNUSED: we actually sometimes want Refl vs. Keep!
||| Smart constructor. We should use this to maximise the length
||| of the Refl segment thus getting more short-circuiting behaviours
export
Keep : Thin xs ys -> Thin (x :: xs) (x :: ys)
Keep Refl = Refl
Keep p = Keep p
-}

export
keeps : (args : List a) -> Thin xs ys -> Thin (args ++ xs) (args ++ ys)
keeps [] th = th
keeps (x :: xs) th = Keep (keeps xs th)

||| Compute the thinning getting rid of the listed de Bruijn indices.
-- TODO: is the list of erased arguments guaranteed to be sorted?
-- Should it?
export
removeByIndices :
  (erasedArgs : List Nat) ->
  (args : Scope) ->
  (args' ** Thin args' args)
removeByIndices es = go 0 where

  go : (currentIdx : Nat) -> (args : Scope) ->
    (args' ** Thin args' args)
  go idx [] = ([] ** Refl)
  go idx (x :: xs) =
    let (vs ** th) = go (S idx) xs in
    if idx `elem` es
      then (vs ** Drop th)
      else (x :: vs ** Keep th)


------------------------------------------------------------------------
-- Concepts

public export
0 Weakenable : Scoped -> Type
Weakenable tm = {0 vars, ns : Scope} ->
  SizeOf ns -> tm vars -> tm (ns ++ vars)

public export
0 Strengthenable : Scoped -> Type
Strengthenable tm = {0 vars, ns : Scope} ->
  SizeOf ns -> tm (ns ++ vars) -> Maybe (tm vars)

public export
0 GenWeakenable : Scoped -> Type
GenWeakenable tm = {0 outer, ns, local : Scope} ->
  SizeOf local -> SizeOf ns -> tm (local ++ outer) -> tm (local ++ (ns ++ outer))

public export
0 Thinnable : Scoped -> Type
Thinnable tm = {0 xs, ys : Scope} -> tm xs -> Thin xs ys -> tm ys

public export
0 Shrinkable : Scoped -> Type
Shrinkable tm = {0 xs, ys : Scope} -> tm xs -> Thin ys xs -> Maybe (tm ys)

public export
0 Embeddable : Scoped -> Type
Embeddable tm = {0 outer, vars : Scope} -> tm vars -> tm (vars ++ outer)

------------------------------------------------------------------------
-- IsScoped interface

public export
interface Weaken (0 tm : Scoped) where
  constructor MkWeaken
  -- methods
  weaken : tm vars -> tm (nm :: vars)
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
  SizeOf local -> tm (local ++ outer) -> tm (local ++ n :: outer)
genWeaken l = genWeakenNs l (suc zero)

public export
interface Strengthen (0 tm : Scoped) where
  constructor MkStrengthen
  -- methods
  strengthenNs : Strengthenable tm

export
strengthen : Strengthen tm => tm (nm :: vars) -> Maybe (tm vars)
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
compat : IsScoped tm => tm (m :: xs) -> tm (n :: xs)
compat = compatNs (Ext Pre)
