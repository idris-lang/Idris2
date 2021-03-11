module Libraries.Data.IMaybe

%default total

public export
data IMaybe : Bool -> Type -> Type where
  Nothing : IMaybe False a
  Just : a -> IMaybe True a

export
Functor (IMaybe b) where
  map f Nothing = Nothing
  map f (Just x) = Just (f x)

export
fromJust : IMaybe True a -> a
fromJust (Just x) = x
