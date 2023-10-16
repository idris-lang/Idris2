||| Version of Maybe indexed by an `isJust' boolean
module Data.IMaybe

import Data.Zippable

%default total

public export
data IMaybe : Bool -> Type -> Type where
  Just : a -> IMaybe True a
  Nothing : IMaybe False a

public export
fromJust : IMaybe True a -> a
fromJust (Just a) = a

public export
Functor (IMaybe b) where
  map f (Just a) = Just (f a)
  map f Nothing = Nothing

public export
Applicative (IMaybe True) where
  pure = Just
  Just f <*> Just x = Just (f x)

public export
Zippable (IMaybe b) where
  zipWith f Nothing  Nothing  = Nothing
  zipWith f (Just x) (Just y) = Just $ f x y

  zipWith3 f Nothing  Nothing  Nothing  = Nothing
  zipWith3 f (Just x) (Just y) (Just z) = Just $ f x y z

  unzipWith f Nothing  = (Nothing, Nothing)
  unzipWith f (Just x) = let (a, b) = f x in (Just a, Just b)

  unzipWith3 f Nothing  = (Nothing, Nothing, Nothing)
  unzipWith3 f (Just x) = let (a, b, c) = f x in (Just a, Just b, Just c)
