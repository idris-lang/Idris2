import Data.Maybe

data ErasedBind : Type -> Type where
  Impossible : Void => ErasedBind a
  Erased     : forall b. ErasedBind ((0 x : a) -> b x)

f : forall b. ErasedBind ((x : a) -> b x) -> Void
f Impossible impossible

g : (a : Type) -> ErasedBind a -> Maybe Void
g (a -> b) e = Just (f e)
g _ _ = Nothing

boom : Void
boom = fromJust $ g ((0 _ : Int) -> Int) Erased
