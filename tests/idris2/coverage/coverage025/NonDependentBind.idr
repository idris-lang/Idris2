import Data.Maybe

data NonDependentBind : Type -> Type where
  Impossible   : Void => NonDependentBind a
  NonDependent : NonDependentBind (a -> b)

f : forall b. NonDependentBind ((x : a) -> b x) -> Void
f Impossible impossible

g : (a : Type) -> NonDependentBind a -> Maybe Void
g (a -> b) e = Just (f e)
g _ _ = Nothing

boom : Void
boom = fromJust $ g (Int -> Int) NonDependent
