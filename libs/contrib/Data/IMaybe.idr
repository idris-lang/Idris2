||| Version of Maybe indexed by an `isJust' boolean
module Data.IMaybe

%default total

public export
data IMaybe : Bool -> Type -> Type where
  Just : a -> IMaybe True a
  Nothing : IMaybe False a

public export
Cast (IMaybe True a) a where
  cast (Just a) = a

public export
Functor (IMaybe b) where
  map f (Just a) = Just (f a)
  map f Nothing = Nothing

public export
Applicative (IMaybe True) where
  pure = Just
  Just f <*> Just x = Just (f x)
