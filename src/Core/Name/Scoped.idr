module Core.Name.Scoped

import Core.Name
import Data.SnocList
import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

%default total

------------------------------------------------------------------------
-- Basic type definitions

||| A scope is a left-nested list of names. E.g. in the following
||| rule, the scope Γ is extended with x when going under the λx.
||| binder:
|||
|||    Γ, x ⊢ t : B
|||  -----------------------------
|||    Γ    ⊢ λx. t : A → B
public export
Scope : Type
Scope = SnocList Name


||| A local scope extension corresponds to a non-empty list of
||| binders brought into scope; typically in a case branch.
||| If the constructor C takes n arguments, the branch b of
||| a case alternative matching on it and binding its n arguments
||| will be typed under a local extension [x1, ..., xn].
|||
|||     Γ, x1, ..., xn ⊢ b   (...)
||| ---------------------------------------------------
|||     Γ              ⊢ case x of C x1 ... xn => b
|||
||| The result scope is written Γ, x1, ..., xn informally and
||| (Γ <>< xs) in Idris.

public export
Local : Type
Local = List Name


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
localEq : (xs, ys : Local) -> Maybe (xs = ys)
localEq [] [] = Just Refl
localEq (x :: xs) (y :: ys)
    = do Refl <- nameEq x y
         Refl <- localEq xs ys
         Just Refl
localEq _ _ = Nothing

------------------------------------------------------------------------
-- Generate a fresh name (for a given scope)

export
uniqueLocal : Scope -> Name -> Name
uniqueLocal vs n
  = if n `elem` vs
    then assert_total $ uniqueLocal vs (next n)
    else n


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
  Keep : Thin xs ys -> Thin (xs :< x) (ys :< x)

export
none : {sx : SnocList a} -> Thin [<] sx
none {sx = [<]} = Refl
none {sx = _ :< _} = Drop none

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

export
keepz : (args : List a) -> Thin xs ys -> Thin (xs <>< args) (ys <>< args)
keepz [] th = th
keepz (x :: xs) th = keepz xs (keep th)

namespace Thin
  -- At runtime, Thin's `Refl` does not carry any additional
  -- information. So this is safe!
  export
  embed : Thin xs ys -> Thin (outer ++ xs) (outer ++ ys)
  embed = believe_me

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
  go idx [<] = ([<] ** Refl)
  go idx (xs :< x) =
    let (vs ** th) = go (S idx) xs in
    if idx `elem` es
      then (vs ** Drop th)
      else (vs :< x ** Keep th)


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
  weaken = weakenNs (suc zero)

-- This cannot be merged with Weaken because of WkCExp
public export
interface GenWeaken (0 tm : Scoped) where
  constructor MkGenWeaken
  genWeakenNs : GenWeakenable tm

export
genWeaken : GenWeaken tm =>
  SizeOf local -> tm (outer ++ local) -> tm (outer :< n ++ local)
genWeaken l = genWeakenNs l (suc zero)

export
genWeakenFishily : GenWeaken tm =>
  SizeOf local -> tm (outer <>< local) -> tm (outer :< n <>< local)
genWeakenFishily l
  = rewrite fishAsSnocAppend outer local in
    rewrite fishAsSnocAppend (outer :< n) local in
    genWeakenNs (zero <>< l) (suc zero)

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
  strengthen : tm (vars :< nm) -> Maybe (tm vars)
  strengthenNs : Strengthenable tm

  -- default implementations
  strengthenNs p t = case sizedView p of
    Z   => pure t
    S p' => strengthenNs p' =<< strengthen t

  strengthen = strengthenNs (suc zero)

export
strengthensN :
  Strengthen tm => SizeOf ns ->
  tm (vars <>< ns) -> Maybe (tm vars)
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
embedFishily : FreelyEmbeddable tm => tm (cast ns) -> tm (vars <>< ns)
embedFishily t = rewrite fishAsSnocAppend vars ns in embed t

export
ListFreelyEmbeddable : FreelyEmbeddable tm => FreelyEmbeddable (List . tm)
ListFreelyEmbeddable = MkFreelyEmbeddable believe_me

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
  compat : tm (xs :< m) -> tm (xs :< n)
  compatNs : CompatibleVars xs ys -> tm xs -> tm ys

  thin : Thinnable tm
  shrink : Shrinkable tm

  -- default implementations
  compat = compatNs (Ext Pre)
