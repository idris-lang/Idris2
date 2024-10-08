module Core.Name.CompatibleVars

public export
data CompatibleVars : (xs, ys : SnocList a) -> Type where
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
extendCompats args Pre = Pre
extendCompats args prf = go args prf where

  go : (args : SnocList a) ->
       CompatibleVars xs ys ->
       CompatibleVars (xs ++ args) (ys ++ args)
  go [<] prf = prf
  go (xs :< x) prf = Ext (go xs prf)

export
decCompatibleVars : (xs, ys : SnocList a) -> Dec (CompatibleVars xs ys)
decCompatibleVars [<] [<] = Yes Pre
decCompatibleVars [<] (xs :< x) = No (\case p impossible)
decCompatibleVars (xs :< x) [<] = No (\case p impossible)
decCompatibleVars (xs :< x) (ys :< y) = case decCompatibleVars xs ys of
  Yes prf => Yes (Ext prf)
  No nprf => No (nprf . invertExt)

export
areCompatibleVars : (xs, ys : SnocList a) ->
                    Maybe (CompatibleVars xs ys)
areCompatibleVars [<] [<] = pure Pre
areCompatibleVars (xs :< x) (ys :< y)
    = do compat <- areCompatibleVars xs ys
         pure (Ext compat)
areCompatibleVars _ _ = Nothing
