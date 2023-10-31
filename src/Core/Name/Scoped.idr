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
data Thin : SnocList Name -> SnocList Name -> Type where
  Refl : Thin xs xs
  Drop : Thin xs ys -> Thin xs (ys :< y)
  Keep : Thin xs ys -> Thin (xs :< x) (ys :< y)

export
keep : Thin xs ys -> Thin (xs :< x) (ys :< x)
keep Refl = Refl
keep p = Keep p

public export
0 Thinnable : Scoped -> Type
Thinnable tm = {0 xs, ys : _} -> tm xs -> Thin xs ys -> tm ys

public export
0 Strengthenable : Scoped -> Type
Strengthenable tm = {0 xs, ys : _} -> tm xs -> Thin ys xs -> Maybe (tm ys)

------------------------------------------------------------------------
-- IsScoped interface

public export
interface IsScoped (0 tm : Scoped) where

  -- methods

  -- this is free for nameless representations
  embedNs : Lazy (SizeOf outer) -> tm vars -> tm (outer ++ vars)

  weaken : tm vars -> tm (vars :< nm)
  weakenNs : SizeOf inner -> tm vars -> tm (vars ++ inner)

  compat : tm (xs :< m) -> tm (xs :< n)
  compatNs : CompatibleVars xs ys -> tm xs -> tm ys

  thin : Thinnable tm
  strengthen : Strengthenable tm

  -- default implementations

  weakenNs p t = case sizedView p of
    Z   => t
    S p => weaken (weakenNs p t)

  weaken = weakenNs (suc zero)

  compat = compatNs (Ext Pre)
