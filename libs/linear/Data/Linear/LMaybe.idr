module Data.Linear.LMaybe

import Data.Linear.Notation

%default total

||| Linear version of Maybe
public export
data LMaybe : Type -> Type where
  Nothing : LMaybe a
  Just : a -@ LMaybe a

export
(<$>) : (a -@ b) -> LMaybe a -@ LMaybe b
f <$> Nothing = Nothing
f <$> Just x = Just (f x)
