module Core.Name.Scoped

import Core.Name
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

%default total

public export
Scoped : Type
Scoped = SnocList Name -> Type

public export
interface Weaken (0 tm : Scoped) where
  weaken : tm vars -> tm (vars :< nm)
  weakenNs : SizeOf ns -> tm vars -> tm (vars ++ ns)

  weakenNs p t = case sizedView p of
    Z   => t
    S p => weaken (weakenNs p t)

  weaken = weakenNs (suc zero)
