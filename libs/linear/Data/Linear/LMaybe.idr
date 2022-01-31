module Data.Linear.LMaybe

import Data.Linear.Bifunctor
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

export
Consumable a => Consumable (LMaybe a) where
  consume Nothing = ()
  consume (Just a) = consume a

export
Duplicate a => Duplicate (LMaybe a) where
  dup Nothing = Nothing # Nothing
  dup (Just a) = bimap Just Just (Notation.dup a)
