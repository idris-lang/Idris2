module Core.Name.CompatibleVars

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
